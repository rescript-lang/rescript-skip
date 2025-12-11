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
  let live = Set.fromArray(getLiveSet(service))
  service.nodes->Array.filter(node => !(live->Set.has(node)))
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
let logCounts = (label, service) => {
  let live = getLiveSet(service)
  let dead = getDeadSet(service)
  Console.log2(
    label,
    {
      "live": live->Array.length,
      "dead": dead->Array.length,
    },
  )
}

// Naive BFS reachability from roots - general algorithm that works on any graph
let naiveReachability = (~roots: array<int>, ~edges: Map.t<int, array<int>>, ~nodeCount: int) => {
  let visited = Set.make()
  let queue = []

  // Start from all roots
  roots->Array.forEach(root => {
    if !(visited->Set.has(root)) {
      visited->Set.add(root)->ignore
      queue->Array.push(root)->ignore
    }
  })

  // BFS traversal
  let head = ref(0)
  while head.contents < queue->Array.length {
    let current = queue->Array.getUnsafe(head.contents)
    head.contents = head.contents + 1

    switch edges->Map.get(current) {
    | Some(neighbors) =>
      neighbors->Array.forEach(neighbor => {
        if !(visited->Set.has(neighbor)) {
          visited->Set.add(neighbor)->ignore
          queue->Array.push(neighbor)->ignore
        }
      })
    | None => ()
    }
  }

  let liveCount = visited->Set.size
  (liveCount, nodeCount - liveCount)
}

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

// ============================================================================
// Demo 2: Alternative Path Survival
// ============================================================================

let alternativePathDemo = () => {
  log("")
  log("Alternative Path Demo")
  log("=====================")
  log("(This tests the edge case that required algorithm revision)")
  log("")

  // Create a graph where 'db' has TWO paths from main:
  //
  //   main → api → db
  //     ↓
  //   backup → db
  //
  // When we remove main → api, db should SURVIVE via main → backup → db

  let service = makeDCEService(
    ~nodes=["main", "api", "backup", "db"],
    ~roots=["main"],
    ~edges=[
      ("main", ["api", "backup"]),
      ("api", ["db"]),
      ("backup", ["db"]),
    ],
  )

  log("Graph with redundant paths to db:")
  log("  main → api → db")
  log("  main → backup → db")
  log("")

  logArray("Live set", getLiveSet(service))
  logArray("Dead set", getDeadSet(service))
  log("")

  // Remove the direct path main → api
  log("--- Remove edge main → api ---")
  log("    (db should survive via backup path)")
  let changes = removeEdge(service, "main", "api")
  logArray("Removed", changes.removed)
  logArray("Live set", getLiveSet(service))
  log("")

  // Verify db is still live
  let dbIsLive = getLiveSet(service)->Array.includes("db")
  if dbIsLive {
    log("✓ CORRECT: db survived via alternative path (main → backup → db)")
  } else {
    log("✗ BUG: db was incorrectly removed!")
  }
  log("")

  // Now remove the backup path too - db should die
  log("--- Remove edge backup → db ---")
  log("    (now db has no path from main)")
  let changes2 = removeEdge(service, "backup", "db")
  logArray("Removed", changes2.removed)
  logArray("Live set", getLiveSet(service))
  log("")

  log("Alternative path demo complete!")
}

// ============================================================================
// Stress tests (incremental vs naive full recompute)
// ============================================================================

// Build a tree graph: each node has `branching` children
// Returns (nodeNames, edges as Map, edges as array for DCE service, height)
let buildTreeGraph = (~branching: int, ~height: int) => {
  let edges = Map.make()
  let edgesArray = []
  let nodeNames = []
  
  let nodeId = ref(0)
  
  // BFS to build tree level by level
  let currentLevel = ref([0])
  nodeNames->Array.push("node-0")->ignore
  nodeId.contents = 1
  
  for _level in 1 to height {
    let nextLevel = []
    currentLevel.contents->Array.forEach(parent => {
      let children = []
      for _child in 1 to branching {
        let childId = nodeId.contents
        nodeId.contents = nodeId.contents + 1
        children->Array.push(childId)->ignore
        nextLevel->Array.push(childId)->ignore
        nodeNames->Array.push("node-" ++ childId->Int.toString)->ignore
      }
      edges->Map.set(parent, children)->ignore
      let childNames = children->Array.map(c => "node-" ++ c->Int.toString)
      edgesArray->Array.push(("node-" ++ parent->Int.toString, childNames))->ignore
    })
    currentLevel.contents = nextLevel
  }
  
  (nodeNames, edges, edgesArray, height)
}

// Count nodes in subtree rooted at given node
let countSubtree = (edges: Map.t<int, array<int>>, root: int) => {
  let count = ref(0)
  let queue = [root]
  let head = ref(0)
  while head.contents < queue->Array.length {
    let current = queue->Array.getUnsafe(head.contents)
    head.contents = head.contents + 1
    count.contents = count.contents + 1
    switch edges->Map.get(current) {
    | Some(children) => children->Array.forEach(c => queue->Array.push(c)->ignore)
    | None => ()
    }
  }
  count.contents
}

let stressBenchmark = (
  ~nodeNames: array<string>,
  ~naiveEdges: Map.t<int, array<int>>,
  ~edgesArray: array<(string, array<string>)>,
  ~editCount: int,
  ~cutParent: int,
  ~cutChild: int,
  ~label: string,
) => {
  let nodeCount = nodeNames->Array.length
  log("")
  log("=================================================================")
  log(label)
  log("=================================================================")
  
  let subtreeSize = countSubtree(naiveEdges, cutChild)
  Console.log2("Subtree being cut", {"parent": cutParent, "child": cutChild, "subtree_size": subtreeSize})
  log("")

  // --- Setup for incremental (NOT timed) ---
  log("Setting up incremental service (not timed)...")
  let service = makeDCEService(~nodes=nodeNames, ~roots=["node-0"], ~edges=edgesArray)

  let fromNode = "node-" ++ cutParent->Int.toString
  let toNode = "node-" ++ cutChild->Int.toString

  // Store original children for naive
  let originalChildren = naiveEdges->Map.get(cutParent)->Option.getOr([])

  // Verify initial state
  let incInitLive = getLiveSet(service)->Array.length
  Console.log2("Initial", {"live": incInitLive, "dead": nodeCount - incInitLive})
  log("")

  // --- Incremental: measure edits ---
  log("--- Incremental: " ++ editCount->Int.toString ++ " edits ---")
  let incTotalMs = ref(0.0)
  for edit in 1 to editCount {
    let startMs = Date.now()
    if Int.mod(edit, 2) == 1 {
      removeEdge(service, fromNode, toNode)->ignore
    } else {
      addEdge(service, fromNode, toNode)->ignore
    }
    let elapsedMs = Date.now() -. startMs
    incTotalMs.contents = incTotalMs.contents +. elapsedMs
    // Show first few edits as examples
    if edit <= 4 {
      let live = getLiveSet(service)->Array.length
      let dead = nodeCount - live
      let action = if Int.mod(edit, 2) == 1 { "remove" } else { "add" }
      Console.log2(
        "  Edit " ++ edit->Int.toString ++ " (" ++ action ++ ")",
        {"ms": elapsedMs, "live": live, "dead": dead},
      )
    } else if edit == 5 {
      log("  ...")
    }
  }
  let incFinalLive = getLiveSet(service)->Array.length
  let incFinalDead = nodeCount - incFinalLive
  Console.log2("  Final state", {"live": incFinalLive, "dead": incFinalDead})
  log("")

  // --- Naive BFS: measure edits ---
  log("--- Naive BFS: " ++ editCount->Int.toString ++ " edits with full recompute ---")
  let naiveTotalMs = ref(0.0)
  let naiveRoots = [0]
  let naiveLive = ref(0)
  let naiveDead = ref(0)
  for edit in 1 to editCount {
    // Apply the edit: remove or restore the child
    if Int.mod(edit, 2) == 1 {
      let withoutChild = originalChildren->Array.filter(c => c != cutChild)
      naiveEdges->Map.set(cutParent, withoutChild)->ignore
    } else {
      naiveEdges->Map.set(cutParent, originalChildren)->ignore
    }
    // Time the full recompute
    let startMs = Date.now()
    let (live, dead) = naiveReachability(~roots=naiveRoots, ~edges=naiveEdges, ~nodeCount)
    let elapsedMs = Date.now() -. startMs
    naiveTotalMs.contents = naiveTotalMs.contents +. elapsedMs
    naiveLive.contents = live
    naiveDead.contents = dead
    // Show first few edits as examples
    if edit <= 4 {
      let action = if Int.mod(edit, 2) == 1 { "remove" } else { "add" }
      Console.log2(
        "  Edit " ++ edit->Int.toString ++ " (" ++ action ++ ")",
        {"ms": elapsedMs, "live": live, "dead": dead},
      )
    } else if edit == 5 {
      log("  ...")
    }
  }
  Console.log2("  Final state", {"live": naiveLive.contents, "dead": naiveDead.contents})
  
  // Restore edges for next test
  naiveEdges->Map.set(cutParent, originalChildren)->ignore
  log("")

  // Summary
  let speedup = naiveTotalMs.contents /. incTotalMs.contents
  Console.log2(
    "TOTAL",
    {
      "incremental_ms": incTotalMs.contents,
      "naive_ms": naiveTotalMs.contents,
      "speedup": speedup,
    },
  )
  if speedup > 1.0 {
    log("✓ Incremental is " ++ speedup->Float.toFixed(~digits=1) ++ "x faster")
  } else {
    log("✗ Naive is " ++ (1.0 /. speedup)->Float.toFixed(~digits=1) ++ "x faster")
  }
}

let runBenchmarks = () => {
  log("")
  log("DCE Benchmark: Incremental vs Naive BFS Reachability")
  log("=====================================================")
  log("")
  log("Graph: Tree with branching factor 10, height 5")
  log("  - This models a realistic call graph")
  log("  - Height 5 = max call chain depth of 5")
  log("")
  
  // Build tree: branching=10, height=5 gives 1+10+100+1000+10000+100000 = 111,111 nodes
  let (nodeNames, naiveEdges, edgesArray, height) = buildTreeGraph(~branching=10, ~height=5)
  let nodeCount = nodeNames->Array.length
  Console.log2("Tree structure", {"nodes": nodeCount, "branching": 10, "height": height})
  log("")
  log("Complexity:")
  log("- Incremental: O(affected subtree size)")
  log("- Naive BFS: O(total nodes) every time")
  log("")

  // Scenario 1: Cut a leaf's parent edge (affects 1 node)
  // Pick a node at depth 5 (leaf level) - node 11111 is first leaf
  // Its parent is at depth 4
  let leafNode = 11111  // A leaf node
  let leafParent = 1111 // Its parent
  stressBenchmark(
    ~nodeNames,
    ~naiveEdges,
    ~edgesArray,
    ~editCount=100,
    ~cutParent=leafParent,
    ~cutChild=leafNode,
    ~label="SCENARIO 1: Cut LEAF edge (subtree = 1 node)",
  )

  // Scenario 2: Cut edge at depth 3 (affects ~111 nodes)
  // Node 111 is at depth 3, its parent is 11
  let midNode = 111
  let midParent = 11
  stressBenchmark(
    ~nodeNames,
    ~naiveEdges,
    ~edgesArray,
    ~editCount=100,
    ~cutParent=midParent,
    ~cutChild=midNode,
    ~label="SCENARIO 2: Cut MID-LEVEL edge (subtree = 111 nodes)",
  )

  // Scenario 3: Cut edge near root (affects ~11111 nodes)
  // Node 1 is child of root 0
  let nearRootNode = 1
  let rootNode = 0
  stressBenchmark(
    ~nodeNames,
    ~naiveEdges,
    ~edgesArray,
    ~editCount=10,
    ~cutParent=rootNode,
    ~cutChild=nearRootNode,
    ~label="SCENARIO 3: Cut NEAR-ROOT edge (subtree = 11111 nodes)",
  )

  log("")
  log("=================================================================")
  log("CONCLUSION")
  log("=================================================================")
  log("Incremental wins when editing deep in the tree (small subtrees).")
  log("This is the common case: most code edits affect leaf functions.")
  log("")
}

demo()
alternativePathDemo()
runBenchmarks()
