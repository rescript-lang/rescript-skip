/**
 * Incremental Fixpoint Computation (Low-Level API)
 * 
 * **NOTE**: This is a low-level module. Most users should use `SkipruntimeFixpoint`
 * instead, which provides a safer managed API with no user obligations.
 * 
 * This module implements the incremental fixpoint algorithm as described in
 * `incremental_fixpoint_notes.tex` and proven correct in `IncrementalFixpoint.lean`.
 * 
 * ## When to Use This Module
 * 
 * Use this low-level API only when:
 * - You need maximum control over the step relation
 * - The step relation is stored externally (e.g., database, external service)
 * - You're building a higher-level abstraction on top
 * 
 * For most use cases, prefer `SkipruntimeFixpoint` which eliminates user obligations.
 * 
 * ## User Obligations (IMPORTANT)
 * 
 * Correctness depends on the following guarantees from the caller:
 * 
 * 1. **stepFwdForEach stability**: During any single API call (`make` or `applyDelta`),
 *    `stepFwdForEach(x, f)` must call `f` on consistent successors for any `x`. 
 *    If it reads from mutable external state that changes during an operation, 
 *    the algorithm may produce incorrect results.
 * 
 * 2. **Delta accuracy**: When calling `applyDelta`, the delta must accurately
 *    describe changes to the step relation:
 *    - `addedToStep`: pairs (x, y) where y is NOW a successor of x but wasn't before
 *    - `removedFromStep`: pairs (x, y) where y WAS a successor of x but no longer is
 *    - `stepFwdForEach` must ALREADY reflect the new state when `applyDelta` is called
 * 
 * ## Overview
 * 
 * The fixpoint combinator maintains the least fixpoint of a monotone operator:
 * 
 * ```
 * F(S) = base ∪ step(S)
 * ```
 * 
 * where `step(S) = ⋃{stepFwd(x) | x ∈ S}`.
 * 
 * ## Key Operations
 * 
 * - **Expansion**: When F grows (base or step increases), iterate upward via BFS.
 *   Complexity: O(|new elements| + |derivations from new elements|)
 * 
 * - **Contraction**: When F shrinks (base or step decreases), cascade removal using
 *   well-founded derivation (rank-based), followed by re-derivation to handle stale ranks.
 *   Complexity: O(|removed elements| + |derivations to removed elements|)
 * 
 * ## Cycle Handling
 * 
 * The rank of an element is its BFS distance from base. This is essential for
 * contraction: cycle members have equal ranks, so they cannot provide well-founded
 * support to each other, ensuring unreachable cycles are correctly removed.
 * 
 * ## Usage Example
 * 
 * ```rescript
 * // Define the step function (e.g., graph successors)
 * // NOTE: edges must be stable during each operation
 * let edges = ref(Map.make())
 * edges.contents->Map.set("R", Set.fromArray(["A"]))
 * edges.contents->Map.set("A", Set.fromArray(["B"]))
 * 
 * let config: Fixpoint.config<string> = {
 *   stepFwdForEach: (node, f) => {
 *     switch edges.contents->Map.get(node) {
 *     | Some(successors) => successors->Set.forEach(f)
 *     | None => ()
 *     }
 *   },
 * }
 * 
 * // Create initial fixpoint from base elements
 * let state = Fixpoint.make(~config, ~base=["R"])
 * 
 * // Query the fixpoint
 * let elements = Fixpoint.current(state)
 * let isLive = Fixpoint.has(state, "A")
 * 
 * // To apply changes: FIRST update edges, THEN call applyDelta
 * edges.contents->Map.get("A")->Option.forEach(s => s->Set.add("C"))
 * let changes = Fixpoint.applyDelta(state, {
 *   ...Fixpoint.emptyDelta(),
 *   addedToStep: [("A", "C")],
 * })
 * ```
 * 
 * ## References
 * 
 * - `incremental_fixpoint_notes.tex` - Theoretical foundation and algorithms
 * - `IncrementalFixpoint.lean` - Formal correctness proofs
 */

// ============================================================================
// Types
// ============================================================================

/**
 * Configuration for the fixpoint computation.
 * 
 * The user provides:
 * - `stepFwdForEach`: Iteration function over successors. Given element x and
 *   callback f, calls f(y) for each y that is a successor of x.
 *   This is more efficient than returning an array when just iterating.
 * 
 * The inverse function `stepInv` is computed and maintained automatically.
 */
type config<'a> = {
  stepFwdForEach: ('a, 'a => unit) => unit,
}

/**
 * Opaque state maintained by the fixpoint algorithm.
 * 
 * Internally tracks:
 * - `current`: The current fixpoint set = lfp(F)
 * - `rank`: BFS distance from base for each element (for contraction)
 * - `base`: Current base/seed elements
 * - `invIndex`: Computed inverse index for efficient predecessor lookup
 */
type state<'a>

/**
 * Delta representing changes to the fixpoint operator F.
 * 
 * Since F(S) = base ∪ step(S), changes to F come from:
 * 
 * 1. **Changes to base** (seed elements added/removed)
 * 2. **Changes to step** (derivation pairs added/removed)
 * 
 * A step pair (source, target) means "source derives target",
 * i.e., target is a successor of source.
 */
type delta<'a> = {
  /** Elements added to the base set (seeds/roots) */
  addedToBase: array<'a>,
  /** Elements removed from the base set */
  removedFromBase: array<'a>,
  /** Derivation pairs added: (source, target) means target is now a successor of source */
  addedToStep: array<('a, 'a)>,
  /** Derivation pairs removed: (source, target) means target is no longer a successor of source */
  removedFromStep: array<('a, 'a)>,
}

/**
 * Changes produced by applying a delta to the fixpoint.
 */
type changes<'a> = {
  /** Elements added to the fixpoint */
  added: array<'a>,
  /** Elements removed from the fixpoint */
  removed: array<'a>,
}

// ============================================================================
// Constants
// ============================================================================

/**
 * Create an empty delta (no changes to the operator).
 * 
 * Useful as a base for constructing deltas with spread syntax:
 * ```rescript
 * { ...Fixpoint.emptyDelta(), addedToBase: ["newRoot"] }
 * ```
 */
let emptyDelta: unit => delta<'a>

/**
 * Create empty changes (nothing added or removed).
 */
let emptyChanges: unit => changes<'a>

// ============================================================================
// Core API
// ============================================================================

/**
 * Create a new fixpoint state from initial configuration.
 * 
 * Runs BFS expansion to compute the initial fixpoint lfp(F)
 * where F(S) = base ∪ step(S).
 * 
 * @param config - Configuration with the stepFwdForEach function
 * @param base - Initial base/seed elements
 * @returns The fixpoint state with current = lfp(F)
 */
let make: (~config: config<'a>, ~base: array<'a>) => state<'a>

/**
 * Get the current fixpoint as an array of elements.
 */
let current: state<'a> => array<'a>

/**
 * Get the rank of an element.
 * 
 * Rank = BFS distance from base in the iterative construction.
 * Returns None if the element is not in the fixpoint.
 */
let rank: (state<'a>, 'a) => option<int>

/**
 * Check if an element is in the current fixpoint.
 */
let has: (state<'a>, 'a) => bool

/**
 * Get the current size of the fixpoint.
 */
let size: state<'a> => int

/**
 * Apply a delta to the fixpoint and return the changes.
 * 
 * Handles changes to the operator F(S) = base ∪ step(S) in three phases:
 * 
 * 1. **Contraction phase** (F shrinks):
 *    - Process `removedFromBase` and `removedFromStep`
 *    - Run well-founded cascade to remove unsupported elements
 * 
 * 2. **Re-derivation phase** (handles stale ranks):
 *    - Check if any removed element can be re-derived from survivors
 *    - Recovers elements incorrectly removed due to stale ranks
 * 
 * 3. **Expansion phase** (F grows):
 *    - Process `addedToBase` and `addedToStep`
 *    - Run BFS to add newly reachable elements
 * 
 * @param state - The fixpoint state (mutated in place)
 * @param delta - The changes to apply
 * @returns The elements that were added and removed
 */
let applyDelta: (state<'a>, delta<'a>) => changes<'a>

// ============================================================================
// Debugging
// ============================================================================

/**
 * Get debug information about the current state.
 * 
 * Useful for testing and debugging. Returns:
 * - `current`: All elements in the fixpoint
 * - `ranks`: Element-to-rank mapping
 * - `base`: Current base elements
 * - `invIndexSize`: Size of the inverse index
 */
let debugInfo: state<'a> => {
  "current": array<'a>,
  "ranks": array<('a, int)>,
  "base": array<'a>,
  "invIndexSize": int,
}



