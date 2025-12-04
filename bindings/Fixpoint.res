/**
 * Incremental Fixpoint Computation (Optimized)
 * 
 * This module implements the incremental fixpoint algorithm using JS native
 * Set and Map for optimal performance:
 * - O(1) membership tests (hash-based)
 * - O(1) amortized add/delete
 * - Zero allocation iteration via forEach callbacks
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
 */

// ============================================================================
// Types
// ============================================================================

/**
 * Configuration for the fixpoint computation.
 * 
 * `stepFwdForEach` iterates over successors without allocating an array.
 * This is more efficient than returning an array when the caller just
 * needs to iterate.
 */
type config<'a> = {
  stepFwdForEach: ('a, 'a => unit) => unit,
}

/**
 * State maintained by the fixpoint algorithm.
 * 
 * Uses JS native Set and Map for O(1) operations:
 * - `current`: Current fixpoint set = lfp(F)
 * - `rank`: BFS distance from base (for contraction)
 * - `invIndex`: Inverse step relation for contraction
 * - `base`: Current base set
 */
type state<'a> = {
  current: Set.t<'a>,
  rank: Map.t<'a, int>,
  invIndex: Map.t<'a, Set.t<'a>>,
  base: Set.t<'a>,
  config: config<'a>,
}

/**
 * Delta representing changes to the fixpoint operator F.
 */
type delta<'a> = {
  addedToBase: array<'a>,
  removedFromBase: array<'a>,
  addedToStep: array<('a, 'a)>,
  removedFromStep: array<('a, 'a)>,
}

/** Changes produced by applying a delta. */
type changes<'a> = {
  added: array<'a>,
  removed: array<'a>,
}

/** Empty delta (no changes). */
let emptyDelta = (): delta<'a> => {
  addedToBase: [],
  removedFromBase: [],
  addedToStep: [],
  removedFromStep: [],
}

/** Empty changes. */
let emptyChanges = (): changes<'a> => {
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
let addToInvIndex = (state: state<'a>, ~source: 'a, ~target: 'a) => {
  switch state.invIndex->Map.get(target) {
  | Some(set) => set->Set.add(source)
  | None => {
      let set = Set.make()
      set->Set.add(source)
      state.invIndex->Map.set(target, set)
    }
  }
}

/**
 * Remove a derivation from the inverse index: invIndex[y] -= {x}
 */
let removeFromInvIndex = (state: state<'a>, ~source: 'a, ~target: 'a) => {
  switch state.invIndex->Map.get(target) {
  | None => ()
  | Some(set) => {
      set->Set.delete(source)->ignore
      if set->Set.size == 0 {
        state.invIndex->Map.delete(target)->ignore
      }
    }
  }
}

/**
 * Iterate over stepInv(x) from the inverse index.
 * Returns elements that derive x: {y | x ∈ stepFwd(y)}
 */
let forEachStepInv = (state: state<'a>, x: 'a, f: 'a => unit): unit => {
  switch state.invIndex->Map.get(x) {
  | None => ()
  | Some(set) => set->Set.forEach(f)
  }
}

// ============================================================================
// Expansion Algorithm (BFS)
// ============================================================================

/**
 * Expand the fixpoint by running BFS from a frontier.
 * 
 * Uses mutable JS array for O(n) accumulation instead of O(n²) Array.concat.
 * Returns the set of newly added elements.
 */
let expand = (state: state<'a>, ~frontier: Set.t<'a>): array<'a> => {
  let added: array<'a> = []
  let currentFrontier = Set.make()
  let nextFrontier = Set.make()
  
  // Initialize current frontier
  frontier->Set.forEach(x => currentFrontier->Set.add(x))
  
  let r = ref(0)

  while currentFrontier->Set.size > 0 {
    // Add all frontier elements to current with rank r
    currentFrontier->Set.forEach(x => {
      if !(state.current->Set.has(x)) {
        state.current->Set.add(x)
        state.rank->Map.set(x, r.contents)
        added->Array.push(x)->ignore
      }
    })

    // Compute next frontier: successors not yet in current
    nextFrontier->Set.clear
    currentFrontier->Set.forEach(x => {
      state.config.stepFwdForEach(x, y => {
        // Update inverse index: record that x derives y
        addToInvIndex(state, ~source=x, ~target=y)
        // Add to next frontier if not already in current
        if !(state.current->Set.has(y)) {
          nextFrontier->Set.add(y)
        }
      })
    })

    // Swap frontiers
    currentFrontier->Set.clear
    nextFrontier->Set.forEach(x => currentFrontier->Set.add(x))
    r := r.contents + 1
  }

  added
}

// ============================================================================
// Contraction Algorithm (Well-Founded Cascade)
// ============================================================================

/**
 * Check if element x has a well-founded deriver in the current set.
 * 
 * y wf-derives x if:
 * - rank(y) < rank(x)  (strictly lower rank)
 * - x ∈ step({y})      (y derives x)
 */
let hasWellFoundedDeriver = (
  state: state<'a>,
  x: 'a,
  ~dying: Set.t<'a>,
): bool => {
  switch state.rank->Map.get(x) {
  | None => false
  | Some(rx) => {
      let found = ref(false)
      // Early exit would be nice, but forEach doesn't support it
      // We could use an exception for early exit, but keep it simple for now
      forEachStepInv(state, x, y => {
        if !found.contents {
          let inCurrent = state.current->Set.has(y)
          let notDying = !(dying->Set.has(y))
          switch state.rank->Map.get(y) {
          | None => ()
          | Some(ry) =>
            if inCurrent && notDying && ry < rx {
              found := true
            }
          }
        }
      })
      found.contents
    }
  }
}

/**
 * Contract the fixpoint by removing elements that lost support.
 * 
 * Returns the set of removed elements.
 */
let contract = (state: state<'a>, ~worklist: Set.t<'a>): array<'a> => {
  let dying = Set.make()
  let currentWorklist = Set.make()
  
  // Initialize worklist
  worklist->Set.forEach(x => currentWorklist->Set.add(x))

  while currentWorklist->Set.size > 0 {
    // Pop an element from worklist (get first via iterator)
    let x = switch currentWorklist->Set.values->Iterator.toArray->Array.get(0) {
    | None => panic("Worklist should not be empty")
    | Some(v) => v
    }
    currentWorklist->Set.delete(x)->ignore

    // Skip if already dying or in base
    if dying->Set.has(x) || state.base->Set.has(x) {
      ()
    } else {
      // Check for well-founded deriver
      let hasSupport = hasWellFoundedDeriver(state, x, ~dying)

      if !hasSupport {
        // x dies: no well-founded support
        dying->Set.add(x)

        // Find dependents: elements z such that x derives z
        // These might lose their well-founded support
        state.config.stepFwdForEach(x, z => {
          if state.current->Set.has(z) && !(dying->Set.has(z)) {
            currentWorklist->Set.add(z)
          }
        })
      }
    }
  }

  // Remove dying elements from current and rank
  let removed: array<'a> = []
  dying->Set.forEach(x => {
    state.current->Set.delete(x)->ignore
    state.rank->Map.delete(x)->ignore
    removed->Array.push(x)->ignore
  })

  removed
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
let make = (~config: config<'a>, ~base: array<'a>): state<'a> => {
  let baseSet = Set.fromArray(base)
  let state = {
    current: Set.make(),
    rank: Map.make(),
    invIndex: Map.make(),
    base: baseSet,
    config,
  }

  // Initial expansion from base
  let initialFrontier = Set.fromArray(base)
  let _ = expand(state, ~frontier=initialFrontier)

  state
}

/**
 * Get the current fixpoint as an array.
 */
let current = (state: state<'a>): array<'a> => {
  state.current->Set.values->Iterator.toArray
}

/**
 * Get the rank of an element (None if not in fixpoint).
 */
let rank = (state: state<'a>, x: 'a): option<int> => {
  state.rank->Map.get(x)
}

/**
 * Check if an element is in the current fixpoint.
 */
let has = (state: state<'a>, x: 'a): bool => {
  state.current->Set.has(x)
}

/**
 * Get the current size of the fixpoint.
 */
let size = (state: state<'a>): int => {
  state.current->Set.size
}

/**
 * Apply a delta to the fixpoint and return the changes.
 */
let applyDelta = (state: state<'a>, delta: delta<'a>): changes<'a> => {
  let allAdded: array<'a> = []
  let allRemoved: array<'a> = []

  // === CONTRACTION PHASE ===

  // 1. Handle removed step pairs (update inverse index)
  delta.removedFromStep->Array.forEach(((source, target)) => {
    removeFromInvIndex(state, ~source, ~target)
  })

  // 2. Handle removed from base
  delta.removedFromBase->Array.forEach(x => {
    state.base->Set.delete(x)->ignore
  })

  // 3. Compute worklist for contraction
  let contractionWorklist = Set.make()

  delta.removedFromBase->Array.forEach(x => {
    if state.current->Set.has(x) {
      contractionWorklist->Set.add(x)
    }
  })

  delta.removedFromStep->Array.forEach(((source, target)) => {
    if state.current->Set.has(source) && state.current->Set.has(target) {
      contractionWorklist->Set.add(target)
    }
  })

  // Run contraction if needed
  let removedSet = Set.make()
  if contractionWorklist->Set.size > 0 {
    let removed = contract(state, ~worklist=contractionWorklist)
    removed->Array.forEach(x => {
      allRemoved->Array.push(x)->ignore
      removedSet->Set.add(x)
    })
  }

  // === EXPANSION PHASE ===

  // 4. Handle added step pairs (update inverse index)
  delta.addedToStep->Array.forEach(((source, target)) => {
    addToInvIndex(state, ~source, ~target)
  })

  // 5. Handle added to base
  delta.addedToBase->Array.forEach(x => {
    state.base->Set.add(x)
  })

  // 6. Compute frontier for expansion
  let expansionFrontier = Set.make()

  delta.addedToBase->Array.forEach(x => {
    if !(state.current->Set.has(x)) {
      expansionFrontier->Set.add(x)
    }
  })

  delta.addedToStep->Array.forEach(((source, target)) => {
    if state.current->Set.has(source) && !(state.current->Set.has(target)) {
      expansionFrontier->Set.add(target)
    }
  })

  // 7. IMPORTANT: Check if any removed element can be re-derived via existing edges
  // OPTIMIZATION: Use invIndex to only check edges TO removed elements (not all edges)
  // This gives O(|removed| + |edges to removed|) instead of O(|surviving| + |edges from surviving|)
  if removedSet->Set.size > 0 {
    removedSet->Set.forEach(y => {
      // Check if any surviving element derives y (using invIndex)
      forEachStepInv(state, y, x => {
        if state.current->Set.has(x) {
          // x is surviving and derives y, so y might be re-derivable
          expansionFrontier->Set.add(y)
        }
      })
    })
  }

  // Run expansion if needed
  if expansionFrontier->Set.size > 0 {
    let added = expand(state, ~frontier=expansionFrontier)
    added->Array.forEach(x => allAdded->Array.push(x)->ignore)
  }

  // 8. Compute net changes (elements that were removed and not re-added)
  let netRemoved: array<'a> = []
  allRemoved->Array.forEach(x => {
    if !(state.current->Set.has(x)) {
      netRemoved->Array.push(x)->ignore
    }
  })

  // Elements that were added and weren't previously there
  let netAdded: array<'a> = []
  allAdded->Array.forEach(x => {
    if !(removedSet->Set.has(x)) {
      netAdded->Array.push(x)->ignore
    }
  })

  {
    added: netAdded,
    removed: netRemoved,
  }
}

/**
 * Get debug information about the current state.
 */
let debugInfo = (state: state<'a>): {
  "current": array<'a>,
  "ranks": array<('a, int)>,
  "base": array<'a>,
  "invIndexSize": int,
} => {
  {
    "current": state.current->Set.values->Iterator.toArray,
    "ranks": state.rank->Map.entries->Iterator.toArray,
    "base": state.base->Set.values->Iterator.toArray,
    "invIndexSize": state.invIndex->Map.size,
  }
}

