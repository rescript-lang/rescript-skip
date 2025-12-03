/**
 * Incremental Fixpoint Computation
 * 
 * This module implements the incremental fixpoint algorithm as described in
 * `incremental_fixpoint_notes.tex` and proven correct in `IncrementalFixpoint.lean`.
 * 
 * The fixpoint combinator maintains the least fixpoint of a monotone operator:
 * 
 *   F(S) = base ∪ step(S)
 *   
 * where step(S) = ⋃{stepFwd(x) | x ∈ S}
 * 
 * Key operations:
 * - **Expansion**: When F grows (base or step increases), iterate upward via BFS
 * - **Contraction**: When F shrinks (base or step decreases), cascade removal using
 *   well-founded derivation (rank-based)
 * 
 * The rank of an element is its BFS distance from base. This is essential for
 * contraction: cycle members have equal ranks, so they cannot provide well-founded
 * support to each other, ensuring unreachable cycles are correctly removed.
 * 
 * See: incremental_fixpoint_notes.tex, Section 3 "Level 1: Low-Level Incremental Fixpoint API"
 */

module Map = Belt.Map
module Set = Belt.Set

// ============================================================================
// API Specification (from incremental_fixpoint_notes.tex Section 3.1)
// ============================================================================

/**
 * Configuration for the fixpoint computation (User Provides).
 * 
 * From the notes:
 * - `base : Set(A)` - Seed elements (e.g., roots)
 * - `stepFwd : A → Set(A)` - Forward derivation: given x, returns elements derived by x
 * 
 * The inverse `stepInv` is computed and maintained automatically by the system.
 * 
 * Define: step(S) = ⋃{stepFwd(x) | x ∈ S} and F(S) = base ∪ step(S)
 */
type config<'a> = {
  stepFwd: 'a => array<'a>,
}

/**
 * State maintained by the fixpoint algorithm (System Maintains).
 * 
 * From the notes:
 * - `current : Set(A)` - Current fixpoint set = lfp(F)
 * - `rank : Map(A, ℕ)` - BFS distance from base (for contraction)
 * 
 * Additionally maintained:
 * - `base` - Current base set
 * - `invIndex` - Computed stepInv: invIndex[y] = {x ∈ current | y ∈ stepFwd(x)}
 */
type state<'a> = {
  mutable current: Set.String.t,
  mutable rank: Map.String.t<int>,
  mutable invIndex: Map.String.t<Set.String.t>,
  mutable base: Set.String.t,
  config: config<string>,
}

/**
 * Delta representing changes to the fixpoint operator F.
 * 
 * Since F(S) = base ∪ step(S), changes to F come from:
 * 1. Changes to base (seed elements added/removed)
 * 2. Changes to step (derivation pairs added/removed)
 * 
 * A step pair (x, y) means "x derives y", i.e., y ∈ stepFwd(x).
 */
type delta = {
  /** Elements added to the base set */
  addedToBase: array<string>,
  /** Elements removed from the base set */
  removedFromBase: array<string>,
  /** Derivation pairs added to step: (x, y) means y is now in stepFwd(x) */
  addedToStep: array<(string, string)>,
  /** Derivation pairs removed from step: (x, y) means y was removed from stepFwd(x) */
  removedFromStep: array<(string, string)>,
}

/** Changes produced by applying a delta. */
type changes = {
  added: array<string>,
  removed: array<string>,
}

/** Empty delta (no changes). */
let emptyDelta: delta = {
  addedToBase: [],
  removedFromBase: [],
  addedToStep: [],
  removedFromStep: [],
}

/** Empty changes. */
let emptyChanges: changes = {
  added: [],
  removed: [],
}

// ============================================================================
// Internal helpers: Inverse index maintenance
// ============================================================================

/**
 * Add a derivation to the inverse index: invIndex[y] += {x}
 * This records that x derives y (y ∈ stepFwd(x)).
 */
let addToInvIndex = (state: state<'a>, ~source: string, ~target: string) => {
  let existing = state.invIndex->Map.String.getWithDefault(target, Set.String.empty)
  state.invIndex = state.invIndex->Map.String.set(target, existing->Set.String.add(source))
}

/**
 * Remove a derivation from the inverse index: invIndex[y] -= {x}
 */
let removeFromInvIndex = (state: state<'a>, ~source: string, ~target: string) => {
  switch state.invIndex->Map.String.get(target) {
  | None => ()
  | Some(set) => {
      let newSet = set->Set.String.remove(source)
      if Set.String.isEmpty(newSet) {
        state.invIndex = state.invIndex->Map.String.remove(target)
      } else {
        state.invIndex = state.invIndex->Map.String.set(target, newSet)
      }
    }
  }
}

/**
 * Get stepInv(x) from the inverse index.
 * Returns {y | x ∈ stepFwd(y)}, i.e., elements that derive x.
 */
let getStepInv = (state: state<'a>, x: string): Set.String.t => {
  state.invIndex->Map.String.getWithDefault(x, Set.String.empty)
}

// ============================================================================
// Expansion Algorithm (BFS)
// From incremental_fixpoint_notes.tex Section 3.2.1
// ============================================================================

/**
 * Expand the fixpoint by running BFS from a frontier.
 * 
 * Algorithm from the notes:
 * ```
 * expand(state, config'):
 *   frontier = config'.base \ state.current
 *   r = 0
 *   while frontier ≠ ∅:
 *     for x in frontier:
 *       state.current.add(x)
 *       state.rank[x] = r
 *     nextFrontier = {}
 *     for x in frontier:
 *       for y in config'.stepFwd(x):
 *         if y ∉ state.current:
 *           nextFrontier.add(y)
 *     frontier = nextFrontier
 *     r += 1
 * ```
 * 
 * Returns the set of newly added elements.
 */
let expand = (state: state<'a>, ~frontier: Set.String.t): array<string> => {
  let added = ref([])
  let currentFrontier = ref(frontier)
  let r = ref(0)

  while !Set.String.isEmpty(currentFrontier.contents) {
    // Add all frontier elements to current with rank r
    currentFrontier.contents->Set.String.forEach(x => {
      if !(state.current->Set.String.has(x)) {
        state.current = state.current->Set.String.add(x)
        state.rank = state.rank->Map.String.set(x, r.contents)
        added := Array.concat(added.contents, [x])
      }
    })

    // Compute next frontier: successors not yet in current
    let nextFrontier = ref(Set.String.empty)
    currentFrontier.contents->Set.String.forEach(x => {
      let successors = state.config.stepFwd(x)
      successors->Array.forEach(y => {
        // Update inverse index: record that x derives y
        addToInvIndex(state, ~source=x, ~target=y)
        // Add to next frontier if not already in current
        if !(state.current->Set.String.has(y)) {
          nextFrontier := nextFrontier.contents->Set.String.add(y)
        }
      })
    })

    currentFrontier := nextFrontier.contents
    r := r.contents + 1
  }

  added.contents
}

// ============================================================================
// Contraction Algorithm (Well-Founded Cascade)
// From incremental_fixpoint_notes.tex Section 3.2.2
// ============================================================================

/**
 * Check if element x has a well-founded deriver in the current set.
 * 
 * From the notes (Definition: Well-Founded Derivation):
 * y wf-derives x if:
 * - rank(y) < rank(x)  (strictly lower rank)
 * - x ∈ step({y})      (y derives x)
 * 
 * The rank check is essential for breaking cycles: cycle members have
 * equal ranks, so they cannot provide well-founded support to each other.
 */
let hasWellFoundedDeriver = (
  state: state<'a>,
  x: string,
  ~dying: Set.String.t,
): bool => {
  let xRank = state.rank->Map.String.get(x)
  switch xRank {
  | None => false // x not in fixpoint, no rank
  | Some(rx) => {
      let derivers = getStepInv(state, x)
      derivers->Set.String.some(y => {
        // y must be in current, not dying, and have strictly lower rank
        let inCurrent = state.current->Set.String.has(y)
        let notDying = !(dying->Set.String.has(y))
        let yRank = state.rank->Map.String.get(y)
        switch yRank {
        | None => false
        | Some(ry) => inCurrent && notDying && ry < rx
        }
      })
    }
  }
}

/**
 * Contract the fixpoint by removing elements that lost support.
 * 
 * Algorithm from the notes:
 * ```
 * contract(state, config'):
 *   worklist = { x | x lost support }
 *   dying = {}
 * 
 *   while worklist ≠ ∅:
 *     x = worklist.pop()
 *     if x ∈ dying or x ∈ config'.base: continue
 * 
 *     // Check for well-founded deriver (strictly lower rank)
 *     hasSupport = false
 *     for y in config'.stepInv(x):
 *       if y ∈ (state.current \ dying) and state.rank[y] < state.rank[x]:
 *         hasSupport = true
 *         break
 * 
 *     if not hasSupport:
 *       dying.add(x)
 *       // Notify dependents
 *       for z where x ∈ config'.stepInv(z):
 *         worklist.add(z)
 * 
 *   state.current -= dying
 * ```
 * 
 * Returns the set of removed elements.
 */
let contract = (state: state<'a>, ~worklist: Set.String.t): array<string> => {
  let dying = ref(Set.String.empty)
  let currentWorklist = ref(worklist)

  while !Set.String.isEmpty(currentWorklist.contents) {
    // Pop an element from worklist
    let x = switch currentWorklist.contents->Set.String.minimum {
    | None => ""
    | Some(v) => v
    }
    currentWorklist := currentWorklist.contents->Set.String.remove(x)

    // Skip if already dying or in base
    if dying.contents->Set.String.has(x) || state.base->Set.String.has(x) {
      // Continue to next iteration
      ()
    } else {
      // Check for well-founded deriver
      let hasSupport = hasWellFoundedDeriver(state, x, ~dying=dying.contents)

      if !hasSupport {
        // x dies: no well-founded support
        dying := dying.contents->Set.String.add(x)

        // Find dependents: elements z such that x derives z
        // These might lose their well-founded support
        let successors = state.config.stepFwd(x)
        successors->Array.forEach(z => {
          if state.current->Set.String.has(z) && !(dying.contents->Set.String.has(z)) {
            currentWorklist := currentWorklist.contents->Set.String.add(z)
          }
        })
      }
    }
  }

  // Remove dying elements from current and rank
  dying.contents->Set.String.forEach(x => {
    state.current = state.current->Set.String.remove(x)
    state.rank = state.rank->Map.String.remove(x)
  })

  dying.contents->Set.String.toArray
}

// ============================================================================
// Public API
// ============================================================================

/**
 * Create a new fixpoint state from initial configuration.
 * 
 * Runs BFS expansion to compute the initial fixpoint lfp(F)
 * where F(S) = base ∪ step(S).
 */
let make = (~config: config<string>, ~base: array<string>): state<string> => {
  let state = {
    current: Set.String.empty,
    rank: Map.String.empty,
    invIndex: Map.String.empty,
    base: Set.String.fromArray(base),
    config,
  }

  // Initial expansion from base
  let _ = expand(state, ~frontier=state.base)

  state
}

/**
 * Get the current fixpoint as an array.
 */
let current = (state: state<'a>): array<string> => {
  state.current->Set.String.toArray
}

/**
 * Get the rank of an element (None if not in fixpoint).
 * Rank = BFS distance from base in the iterative construction.
 */
let rank = (state: state<'a>, x: string): option<int> => {
  state.rank->Map.String.get(x)
}

/**
 * Check if an element is in the current fixpoint.
 */
let has = (state: state<'a>, x: string): bool => {
  state.current->Set.String.has(x)
}

/**
 * Get the current size of the fixpoint.
 */
let size = (state: state<'a>): int => {
  state.current->Set.String.size
}

/**
 * Apply a delta to the fixpoint and return the changes.
 * 
 * Handles changes to the operator F(S) = base ∪ step(S):
 * 
 * 1. **Contraction phase** (F shrinks):
 *    - removedFromBase: elements lose base membership
 *    - removedFromStep: derivation pairs removed
 *    → Run well-founded cascade to remove unsupported elements
 * 
 * 2. **Expansion phase** (F grows):
 *    - addedToBase: new seed elements
 *    - addedToStep: new derivation pairs
 *    → Run BFS to add newly reachable elements
 */
let applyDelta = (state: state<string>, delta: delta): changes => {
  let allAdded = ref([])
  let allRemoved = ref([])

  // === CONTRACTION PHASE ===

  // 1. Handle removed step pairs (update inverse index)
  delta.removedFromStep->Array.forEach(((source, target)) => {
    removeFromInvIndex(state, ~source, ~target)
  })

  // 2. Handle removed from base
  let removedBaseSet = Set.String.fromArray(delta.removedFromBase)
  state.base = state.base->Set.String.diff(removedBaseSet)

  // 3. Compute worklist for contraction
  // Elements that might have lost support:
  // - Elements removed from base (if they were in current)
  // - Targets of removed step pairs (if source was in current)
  let contractionWorklist = ref(Set.String.empty)

  delta.removedFromBase->Array.forEach(x => {
    if state.current->Set.String.has(x) {
      contractionWorklist := contractionWorklist.contents->Set.String.add(x)
    }
  })

  delta.removedFromStep->Array.forEach(((source, target)) => {
    if state.current->Set.String.has(source) && state.current->Set.String.has(target) {
      contractionWorklist := contractionWorklist.contents->Set.String.add(target)
    }
  })

  // Run contraction if needed
  if !Set.String.isEmpty(contractionWorklist.contents) {
    let removed = contract(state, ~worklist=contractionWorklist.contents)
    allRemoved := Array.concat(allRemoved.contents, removed)
  }

  // === EXPANSION PHASE ===

  // 4. Handle added step pairs (update inverse index)
  delta.addedToStep->Array.forEach(((source, target)) => {
    addToInvIndex(state, ~source, ~target)
  })

  // 5. Handle added to base
  let addedBaseSet = Set.String.fromArray(delta.addedToBase)
  state.base = state.base->Set.String.union(addedBaseSet)

  // 6. Compute frontier for expansion
  // - New base elements not yet in current
  // - Targets of added step pairs where source is in current
  let expansionFrontier = ref(Set.String.empty)

  delta.addedToBase->Array.forEach(x => {
    if !(state.current->Set.String.has(x)) {
      expansionFrontier := expansionFrontier.contents->Set.String.add(x)
    }
  })

  delta.addedToStep->Array.forEach(((source, target)) => {
    if state.current->Set.String.has(source) && !(state.current->Set.String.has(target)) {
      expansionFrontier := expansionFrontier.contents->Set.String.add(target)
    }
  })

  // Run expansion if needed
  if !Set.String.isEmpty(expansionFrontier.contents) {
    let added = expand(state, ~frontier=expansionFrontier.contents)
    allAdded := Array.concat(allAdded.contents, added)
  }

  {
    added: allAdded.contents,
    removed: allRemoved.contents,
  }
}

/**
 * Get debug information about the current state.
 */
let debugInfo = (state: state<'a>): {
  "current": array<string>,
  "ranks": array<(string, int)>,
  "base": array<string>,
  "invIndexSize": int,
} => {
  {
    "current": state.current->Set.String.toArray,
    "ranks": state.rank->Map.String.toArray,
    "base": state.base->Set.String.toArray,
    "invIndexSize": state.invIndex->Map.String.size,
  }
}
