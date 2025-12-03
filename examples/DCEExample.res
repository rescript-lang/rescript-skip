/**
 * Dead Code Elimination Example
 * 
 * This demonstrates using the managed fixpoint API for reactive DCE.
 * 
 * DCE maintains a "live set" of code units reachable from entry points (roots).
 * When the dependency graph changes, the live set updates incrementally:
 * - Adding edges/roots → expansion (BFS propagation)
 * - Removing edges/roots → contraction (well-founded cascade)
 * 
 * This example uses SkipruntimeFixpoint which owns the step relation,
 * so we don't need to manually keep data and deltas synchronized.
 * 
 * Run with: node examples/DCEExample.res.js
 */
module Set = Belt.Set

// ============================================================================
// DCE Service (using managed fixpoint)
// ============================================================================

/**
 * A reactive DCE service that maintains the live set incrementally.
 * 
 * Uses SkipruntimeFixpoint which owns the step relation (edges),
 * so we only need to track the nodes for dead set computation.
 */
type dceService = {
  nodes: array<string>,
  fixpoint: SkipruntimeFixpoint.t,
}

/**
 * Create a DCE service with initial nodes, roots, and edges.
 */
let makeDCEService = (
  ~nodes: array<string>,
  ~roots: array<string>,
  ~edges: array<(string, array<string>)>,
): dceService => {
  // Create managed fixpoint with initial roots
  let fixpoint = SkipruntimeFixpoint.make(~base=roots)

  // Add all initial edges
  edges->Array.forEach(((from, targets)) => {
    targets->Array.forEach(to_ => {
      fixpoint->SkipruntimeFixpoint.addToStep(~source=from, ~target=to_)->ignore
    })
  })

  {nodes, fixpoint}
}

/**
 * Get the current live set.
 */
let getLiveSet = (service: dceService): array<string> => {
  service.fixpoint->SkipruntimeFixpoint.current
}

/**
 * Get the current dead set (nodes not in the live set).
 */
let getDeadSet = (service: dceService): array<string> => {
  let live = Set.String.fromArray(getLiveSet(service))
  service.nodes->Array.filter(node => !(live->Set.String.has(node)))
}

/**
 * Add a new root (entry point).
 */
let addRoot = (service: dceService, root: string): SkipruntimeFixpoint.changes => {
  service.fixpoint->SkipruntimeFixpoint.addToBase(root)
}

/**
 * Remove a root.
 */
let removeRoot = (service: dceService, root: string): SkipruntimeFixpoint.changes => {
  service.fixpoint->SkipruntimeFixpoint.removeFromBase(root)
}

/**
 * Add an edge (dependency).
 */
let addEdge = (service: dceService, from: string, to_: string): SkipruntimeFixpoint.changes => {
  service.fixpoint->SkipruntimeFixpoint.addToStep(~source=from, ~target=to_)
}

/**
 * Remove an edge.
 */
let removeEdge = (service: dceService, from: string, to_: string): SkipruntimeFixpoint.changes => {
  service.fixpoint->SkipruntimeFixpoint.removeFromStep(~source=from, ~target=to_)
}

// ============================================================================
// Helper functions
// ============================================================================

let log = Console.log
let logArray = (label, arr) =>
  Console.log(label ++ ": [" ++ arr->Array.toSorted(String.compare)->Array.join(", ") ++ "]")

// ============================================================================
// Demo: A small program
// ============================================================================

let demo = () => {
  log("Dead Code Elimination Demo")
  log("==========================")
  log("")

  // Create a simple program graph:
  //
  //   main → utils → helpers
  //     ↓
  //   api → db
  //     ↓
  //   logger
  //
  //   unused1 → unused2  (not reachable from main)

  let service = makeDCEService(
    ~nodes=["main", "utils", "helpers", "api", "db", "logger", "unused1", "unused2"],
    ~roots=["main"],
    ~edges=[
      ("main", ["utils", "api"]),
      ("utils", ["helpers"]),
      ("api", ["db", "logger"]),
      ("unused1", ["unused2"]),
    ],
  )

  log("Initial graph:")
  log("  main → utils, api")
  log("  utils → helpers")
  log("  api → db, logger")
  log("  unused1 → unused2")
  log("")

  logArray("Live set", getLiveSet(service))
  logArray("Dead set", getDeadSet(service))
  log("")

  // Scenario 1: Add a new entry point
  log("--- Add 'unused1' as a new root ---")
  let changes1 = addRoot(service, "unused1")
  logArray("Added", changes1.added)
  logArray("Live set", getLiveSet(service))
  logArray("Dead set", getDeadSet(service))
  log("")

  // Scenario 2: Remove main (leaving only unused1 as root)
  log("--- Remove 'main' root ---")
  let changes2 = removeRoot(service, "main")
  logArray("Removed", changes2.removed)
  logArray("Live set", getLiveSet(service))
  logArray("Dead set", getDeadSet(service))
  log("")

  // Scenario 3: Add main back
  log("--- Add 'main' root back ---")
  let changes3 = addRoot(service, "main")
  logArray("Added", changes3.added)
  logArray("Live set", getLiveSet(service))
  log("")

  // Scenario 4: Remove an edge
  log("--- Remove edge main → api ---")
  let changes4 = removeEdge(service, "main", "api")
  logArray("Removed", changes4.removed)
  logArray("Live set", getLiveSet(service))
  log("")

  // Scenario 5: Add a new edge creating a cycle
  log("--- Add edge helpers → main (creates cycle) ---")
  let _changes5 = addEdge(service, "helpers", "main")
  logArray("Live set", getLiveSet(service))
  log("")

  // Scenario 6: Remove edge that would break cycle reachability
  log("--- Remove edge main → utils ---")
  log("    (helpers → main cycle should die because no wf-deriver)")
  let changes6 = removeEdge(service, "main", "utils")
  logArray("Removed", changes6.removed)
  logArray("Live set", getLiveSet(service))
  log("")

  log("Demo complete!")
}

demo()
