/**
 * Managed Fixpoint for Skip Runtime
 * 
 * This module provides a managed incremental fixpoint API that owns the step
 * relation internally, eliminating the consistency burden on users.
 * 
 * ## Overview
 * 
 * The fixpoint computes lfp(F) where F(S) = base ∪ step(S).
 * 
 * Unlike the low-level `Fixpoint` module where users must keep `stepFwd` and
 * deltas synchronized, this module owns the step relation and provides mutation
 * methods that automatically maintain consistency.
 * 
 * ## Usage
 * 
 * ```rescript
 * // Create a fixpoint with initial base elements
 * let fp = SkipruntimeFixpoint.make(~base=["root"])
 * 
 * // Add edges (step relations)
 * let _ = fp->SkipruntimeFixpoint.addToStep(~source="root", ~target="a")
 * let _ = fp->SkipruntimeFixpoint.addToStep(~source="a", ~target="b")
 * 
 * // Query the fixpoint
 * let isLive = fp->SkipruntimeFixpoint.has("b")  // true
 * let elements = fp->SkipruntimeFixpoint.current()  // ["root", "a", "b"]
 * 
 * // Remove an edge - automatically cascades removal
 * let changes = fp->SkipruntimeFixpoint.removeFromStep(~source="root", ~target="a")
 * // changes.removed = ["a", "b"]
 * ```
 * 
 * ## When to Use
 * 
 * - **This module**: For most use cases. Safe, ergonomic API.
 * - **Fixpoint module**: When you need low-level control or have the step
 *   relation in a different form (e.g., reading from external storage).
 * 
 * ## Comparison with Fixpoint Module
 * 
 * | Aspect | Fixpoint | SkipruntimeFixpoint |
 * |--------|----------|---------------------|
 * | Step relation | User-provided function | Owned internally |
 * | Consistency | User's responsibility | Automatic |
 * | Flexibility | High | Moderate |
 * | Safety | Requires care | Safe by construction |
 */

// ============================================================================
// Types
// ============================================================================

/**
 * Managed fixpoint state (opaque).
 * 
 * Internally maintains both the step relation and the fixpoint algorithm state.
 */
type t

/**
 * Changes produced by a mutation.
 */
type changes = Fixpoint.changes

// ============================================================================
// Creation
// ============================================================================

/**
 * Create a new managed fixpoint.
 * 
 * @param base - Initial base/seed elements
 * @returns A managed fixpoint with the initial fixpoint computed
 * 
 * ## Example
 * 
 * ```rescript
 * let fp = SkipruntimeFixpoint.make(~base=["main", "init"])
 * ```
 */
let make: (~base: array<string>) => t

// ============================================================================
// Mutations
// ============================================================================

/**
 * Add an element to the base set.
 * 
 * Base elements are always in the fixpoint (rank 0).
 * Adding a base element may cause expansion if it has outgoing edges.
 * 
 * @param t - The managed fixpoint
 * @param element - Element to add to base
 * @returns Changes (elements added to the fixpoint)
 */
let addToBase: (t, string) => changes

/**
 * Remove an element from the base set.
 * 
 * Removing a base element may cause contraction if it was the only
 * support for other elements.
 * 
 * @param t - The managed fixpoint
 * @param element - Element to remove from base
 * @returns Changes (elements removed from the fixpoint)
 */
let removeFromBase: (t, string) => changes

/**
 * Add a derivation to the step relation.
 * 
 * This adds the pair (source, target) meaning "source derives target",
 * i.e., target ∈ stepFwd(source).
 * 
 * If source is in the fixpoint, target will be added (expansion).
 * 
 * @param t - The managed fixpoint
 * @param source - The source element
 * @param target - The target element (derived by source)
 * @returns Changes (elements added to the fixpoint)
 * 
 * ## Example
 * 
 * ```rescript
 * // Add edge: main → utils
 * let changes = fp->SkipruntimeFixpoint.addToStep(~source="main", ~target="utils")
 * ```
 */
let addToStep: (t, ~source: string, ~target: string) => changes

/**
 * Remove a derivation from the step relation.
 * 
 * This removes the pair (source, target) meaning "source no longer derives target".
 * 
 * If target has no other well-founded support, it will be removed (contraction).
 * 
 * @param t - The managed fixpoint
 * @param source - The source element
 * @param target - The target element
 * @returns Changes (elements removed from the fixpoint)
 * 
 * ## Example
 * 
 * ```rescript
 * // Remove edge: main → utils
 * let changes = fp->SkipruntimeFixpoint.removeFromStep(~source="main", ~target="utils")
 * ```
 */
let removeFromStep: (t, ~source: string, ~target: string) => changes

/**
 * Apply multiple changes at once.
 * 
 * More efficient than calling individual mutation methods when you have
 * multiple changes to apply. Processes contractions before expansions.
 * 
 * @param t - The managed fixpoint
 * @param addedToBase - Elements to add to base
 * @param removedFromBase - Elements to remove from base
 * @param addedToStep - Derivation pairs to add
 * @param removedToStep - Derivation pairs to remove
 * @returns Combined changes (elements added and removed)
 */
let applyChanges: (
  t,
  ~addedToBase: array<string>=?,
  ~removedFromBase: array<string>=?,
  ~addedToStep: array<(string, string)>=?,
  ~removedToStep: array<(string, string)>=?,
) => changes

// ============================================================================
// Queries
// ============================================================================

/**
 * Check if an element is in the current fixpoint.
 */
let has: (t, string) => bool

/**
 * Get all elements in the current fixpoint.
 */
let current: t => array<string>

/**
 * Get the rank of an element (BFS distance from base).
 * Returns None if the element is not in the fixpoint.
 */
let rank: (t, string) => option<int>

/**
 * Get the size of the current fixpoint.
 */
let size: t => int

// ============================================================================
// Debugging
// ============================================================================

/**
 * Get debug information about the current state.
 */
let debugInfo: t => {
  "current": array<string>,
  "ranks": array<(string, int)>,
  "base": array<string>,
  "stepRelationSize": int,
}
