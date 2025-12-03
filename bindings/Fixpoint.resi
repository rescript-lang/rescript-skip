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
 * 1. **stepFwd stability**: During any single API call (`make` or `applyDelta`),
 *    `stepFwd(x)` must return consistent results for any `x`. If `stepFwd` reads
 *    from mutable external state that changes during an operation, the algorithm
 *    may produce incorrect results.
 * 
 * 2. **Delta accuracy**: When calling `applyDelta`, the delta must accurately
 *    describe changes to the step relation:
 *    - `addedToStep`: pairs (x, y) where y is NOW in stepFwd(x) but wasn't before
 *    - `removedFromStep`: pairs (x, y) where y WAS in stepFwd(x) but no longer is
 *    - `stepFwd` must ALREADY reflect the new state when `applyDelta` is called
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
 *   well-founded derivation (rank-based).
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
 * let edges = ref(Map.String.fromArray([("R", ["A"]), ("A", ["B"])]))
 * 
 * let config: Fixpoint.config<string> = {
 *   stepFwd: node => edges.contents->Map.String.getWithDefault(node, []),
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
 * edges := edges.contents->Map.String.set("A", ["B", "C"])  // Add edge A→C
 * let changes = Fixpoint.applyDelta(state, {
 *   ...Fixpoint.emptyDelta,
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
 * - `stepFwd`: Forward derivation function. Given element x, returns the set of
 *   elements derived by x (i.e., y such that y ∈ stepFwd(x)).
 * 
 * The inverse function `stepInv` is computed and maintained automatically.
 */
type config<'a> = {
  stepFwd: 'a => array<'a>,
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
 * i.e., target ∈ stepFwd(source).
 */
type delta = {
  /** Elements added to the base set (seeds/roots) */
  addedToBase: array<string>,
  /** Elements removed from the base set */
  removedFromBase: array<string>,
  /** Derivation pairs added: (source, target) means target is now in stepFwd(source) */
  addedToStep: array<(string, string)>,
  /** Derivation pairs removed: (source, target) means target was removed from stepFwd(source) */
  removedFromStep: array<(string, string)>,
}

/**
 * Changes produced by applying a delta to the fixpoint.
 */
type changes = {
  /** Elements added to the fixpoint */
  added: array<string>,
  /** Elements removed from the fixpoint */
  removed: array<string>,
}

// ============================================================================
// Constants
// ============================================================================

/**
 * Empty delta (no changes to the operator).
 * 
 * Useful as a base for constructing deltas with spread syntax:
 * ```rescript
 * { ...Fixpoint.emptyDelta, addedToBase: ["newRoot"] }
 * ```
 */
let emptyDelta: delta

/**
 * Empty changes (nothing added or removed).
 */
let emptyChanges: changes

// ============================================================================
// Core API
// ============================================================================

/**
 * Create a new fixpoint state from initial configuration.
 * 
 * Runs BFS expansion to compute the initial fixpoint lfp(F)
 * where F(S) = base ∪ step(S).
 * 
 * @param config - Configuration with the stepFwd function
 * @param base - Initial base/seed elements
 * @returns The fixpoint state with current = lfp(F)
 */
let make: (~config: config<string>, ~base: array<string>) => state<string>

/**
 * Get the current fixpoint as an array of elements.
 */
let current: state<'a> => array<string>

/**
 * Get the rank of an element.
 * 
 * Rank = BFS distance from base in the iterative construction.
 * Returns None if the element is not in the fixpoint.
 */
let rank: (state<'a>, string) => option<int>

/**
 * Check if an element is in the current fixpoint.
 */
let has: (state<'a>, string) => bool

/**
 * Get the current size of the fixpoint.
 */
let size: state<'a> => int

/**
 * Apply a delta to the fixpoint and return the changes.
 * 
 * Handles changes to the operator F(S) = base ∪ step(S) in two phases:
 * 
 * 1. **Contraction phase** (F shrinks):
 *    - Process `removedFromBase` and `removedFromStep`
 *    - Run well-founded cascade to remove unsupported elements
 * 
 * 2. **Expansion phase** (F grows):
 *    - Process `addedToBase` and `addedToStep`
 *    - Run BFS to add newly reachable elements
 * 
 * @param state - The fixpoint state (mutated in place)
 * @param delta - The changes to apply
 * @returns The elements that were added and removed
 */
let applyDelta: (state<string>, delta) => changes

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
  "current": array<string>,
  "ranks": array<(string, int)>,
  "base": array<string>,
  "invIndexSize": int,
}

