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
 */

module Map = Belt.Map
module Set = Belt.Set

// ============================================================================
// Types
// ============================================================================

/**
 * Managed fixpoint state.
 * 
 * Internally maintains:
 * - The step relation as explicit data (via ref for closure capture)
 * - The underlying Fixpoint algorithm state
 */
type t = {
  stepRelation: ref<Map.String.t<Set.String.t>>,
  fixpointState: Fixpoint.state<string>,
}

/**
 * Changes produced by a mutation.
 */
type changes = Fixpoint.changes

// ============================================================================
// Internal Helpers
// ============================================================================

/**
 * Get successors from the internal step relation.
 */
let getSuccessors = (stepRelation: Map.String.t<Set.String.t>, source: string): array<string> => {
  stepRelation->Map.String.getWithDefault(source, Set.String.empty)->Set.String.toArray
}

// ============================================================================
// Creation
// ============================================================================

/**
 * Create a new managed fixpoint.
 * 
 * @param base - Initial base/seed elements
 * @returns A managed fixpoint with the initial fixpoint computed
 */
let make = (~base: array<string>): t => {
  // Start with empty step relation (ref for closure capture)
  let stepRelation = ref(Map.String.empty)

  // Create fixpoint config that reads from our internal step relation
  let config: Fixpoint.config<string> = {
    stepFwd: source => getSuccessors(stepRelation.contents, source),
  }

  // Create the underlying fixpoint state
  let fixpointState = Fixpoint.make(~config, ~base)

  {
    stepRelation,
    fixpointState,
  }
}

// ============================================================================
// Mutations
// ============================================================================

/**
 * Add an element to the base set.
 * 
 * @param t - The managed fixpoint
 * @param element - Element to add to base
 * @returns Changes (elements added to the fixpoint)
 */
let addToBase = (t: t, element: string): changes => {
  Fixpoint.applyDelta(
    t.fixpointState,
    {
      ...Fixpoint.emptyDelta,
      addedToBase: [element],
    },
  )
}

/**
 * Remove an element from the base set.
 * 
 * @param t - The managed fixpoint
 * @param element - Element to remove from base
 * @returns Changes (elements removed from the fixpoint)
 */
let removeFromBase = (t: t, element: string): changes => {
  Fixpoint.applyDelta(
    t.fixpointState,
    {
      ...Fixpoint.emptyDelta,
      removedFromBase: [element],
    },
  )
}

/**
 * Add a derivation to the step relation.
 * 
 * This adds the pair (source, target) meaning "source derives target",
 * i.e., target ∈ stepFwd(source).
 * 
 * @param t - The managed fixpoint
 * @param source - The source element
 * @param target - The target element (derived by source)
 * @returns Changes (elements added to the fixpoint)
 */
let addToStep = (t: t, ~source: string, ~target: string): changes => {
  // Update internal step relation
  let existing = t.stepRelation.contents->Map.String.getWithDefault(source, Set.String.empty)
  t.stepRelation := t.stepRelation.contents->Map.String.set(source, existing->Set.String.add(target))

  // Apply delta to fixpoint
  Fixpoint.applyDelta(
    t.fixpointState,
    {
      ...Fixpoint.emptyDelta,
      addedToStep: [(source, target)],
    },
  )
}

/**
 * Remove a derivation from the step relation.
 * 
 * This removes the pair (source, target) meaning "source no longer derives target".
 * 
 * @param t - The managed fixpoint
 * @param source - The source element
 * @param target - The target element
 * @returns Changes (elements removed from the fixpoint)
 */
let removeFromStep = (t: t, ~source: string, ~target: string): changes => {
  // Update internal step relation
  let existing = t.stepRelation.contents->Map.String.getWithDefault(source, Set.String.empty)
  let newSet = existing->Set.String.remove(target)
  if Set.String.isEmpty(newSet) {
    t.stepRelation := t.stepRelation.contents->Map.String.remove(source)
  } else {
    t.stepRelation := t.stepRelation.contents->Map.String.set(source, newSet)
  }

  // Apply delta to fixpoint
  Fixpoint.applyDelta(
    t.fixpointState,
    {
      ...Fixpoint.emptyDelta,
      removedFromStep: [(source, target)],
    },
  )
}

/**
 * Apply multiple changes at once.
 * 
 * More efficient than calling individual mutation methods when you have
 * multiple changes to apply.
 * 
 * @param t - The managed fixpoint
 * @param changes - The changes to apply
 * @returns Combined changes (elements added and removed)
 */
let applyChanges = (
  t: t,
  ~addedToBase: array<string>=[],
  ~removedFromBase: array<string>=[],
  ~addedToStep: array<(string, string)>=[],
  ~removedToStep: array<(string, string)>=[],
): changes => {
  // Update internal step relation for additions
  addedToStep->Array.forEach(((source, target)) => {
    let existing = t.stepRelation.contents->Map.String.getWithDefault(source, Set.String.empty)
    t.stepRelation := t.stepRelation.contents->Map.String.set(source, existing->Set.String.add(target))
  })

  // Update internal step relation for removals
  removedToStep->Array.forEach(((source, target)) => {
    let existing = t.stepRelation.contents->Map.String.getWithDefault(source, Set.String.empty)
    let newSet = existing->Set.String.remove(target)
    if Set.String.isEmpty(newSet) {
      t.stepRelation := t.stepRelation.contents->Map.String.remove(source)
    } else {
      t.stepRelation := t.stepRelation.contents->Map.String.set(source, newSet)
    }
  })

  // Apply delta to fixpoint
  Fixpoint.applyDelta(
    t.fixpointState,
    {
      addedToBase,
      removedFromBase,
      addedToStep,
      removedFromStep: removedToStep,
    },
  )
}

// ============================================================================
// Queries
// ============================================================================

/**
 * Check if an element is in the current fixpoint.
 */
let has = (t: t, element: string): bool => {
  Fixpoint.has(t.fixpointState, element)
}

/**
 * Get all elements in the current fixpoint.
 */
let current = (t: t): array<string> => {
  Fixpoint.current(t.fixpointState)
}

/**
 * Get the rank of an element (BFS distance from base).
 * Returns None if the element is not in the fixpoint.
 */
let rank = (t: t, element: string): option<int> => {
  Fixpoint.rank(t.fixpointState, element)
}

/**
 * Get the size of the current fixpoint.
 */
let size = (t: t): int => {
  Fixpoint.size(t.fixpointState)
}

// ============================================================================
// Debugging
// ============================================================================

/**
 * Get debug information about the current state.
 */
let debugInfo = (t: t): {
  "current": array<string>,
  "ranks": array<(string, int)>,
  "base": array<string>,
  "stepRelationSize": int,
} => {
  let info = Fixpoint.debugInfo(t.fixpointState)
  {
    "current": info["current"],
    "ranks": info["ranks"],
    "base": info["base"],
    "stepRelationSize": t.stepRelation.contents->Map.String.size,
  }
}
