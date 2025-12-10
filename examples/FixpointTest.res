/**
 * Tests for Fixpoint (optimized implementation with JS native collections)
 * 
 * Run with: node examples/FixpointTest.res.js
 */

// ============================================================================
// Test Helpers
// ============================================================================

let testCount = ref(0)
let passCount = ref(0)
let failCount = ref(0)

let sortedArray = arr => arr->Array.toSorted(String.compare)

let assertEqual = (name: string, actual: array<string>, expected: array<string>) => {
  testCount := testCount.contents + 1
  let actualSorted = sortedArray(actual)
  let expectedSorted = sortedArray(expected)
  let pass = actualSorted == expectedSorted
  if pass {
    passCount := passCount.contents + 1
    Console.log("✓ " ++ name)
  } else {
    failCount := failCount.contents + 1
    Console.log("✗ " ++ name)
    Console.log2("  Expected:", expectedSorted)
    Console.log2("  Actual:  ", actualSorted)
  }
}

let assertSize = (name: string, actual: int, expected: int) => {
  testCount := testCount.contents + 1
  if actual == expected {
    passCount := passCount.contents + 1
    Console.log("✓ " ++ name)
  } else {
    failCount := failCount.contents + 1
    Console.log("✗ " ++ name)
    Console.log2("  Expected:", expected)
    Console.log2("  Actual:  ", actual)
  }
}

let assertTrue = (name: string, actual: bool) => {
  testCount := testCount.contents + 1
  if actual {
    passCount := passCount.contents + 1
    Console.log("✓ " ++ name)
  } else {
    failCount := failCount.contents + 1
    Console.log("✗ " ++ name)
    Console.log("  Expected: true, Actual: false")
  }
}

let assertFalse = (name: string, actual: bool) => {
  testCount := testCount.contents + 1
  if !actual {
    passCount := passCount.contents + 1
    Console.log("✓ " ++ name)
  } else {
    failCount := failCount.contents + 1
    Console.log("✗ " ++ name)
    Console.log("  Expected: false, Actual: true")
  }
}

// ============================================================================
// Helper to create config from edge map
// ============================================================================

let makeConfig = (edges: Map.t<string, Set.t<string>>): Fixpoint.config<string> => {
  stepFwdForEach: (source, f) => {
    switch edges->Map.get(source) {
    | None => ()
    | Some(targets) => targets->Set.forEach(f)
    }
  },
}

let makeEdges = (edgeList: array<(string, array<string>)>): Map.t<string, Set.t<string>> => {
  let edges = Map.make()
  edgeList->Array.forEach(((from, targets)) => {
    edges->Map.set(from, Set.fromArray(targets))
  })
  edges
}

// ============================================================================
// Test: Basic Expansion
// ============================================================================

let testBasicExpansion = () => {
  Console.log("")
  Console.log("=== Test: Basic Expansion ===")
  
  // Graph: a -> b -> c
  let edges = makeEdges([("a", ["b"]), ("b", ["c"])])
  let config = makeConfig(edges)
  
  let state = Fixpoint.make(~config, ~base=["a"])
  
  assertEqual("Initial fixpoint contains a, b, c", Fixpoint.current(state), ["a", "b", "c"])
  assertSize("Size is 3", Fixpoint.size(state), 3)
  assertTrue("Has a", Fixpoint.has(state, "a"))
  assertTrue("Has b", Fixpoint.has(state, "b"))
  assertTrue("Has c", Fixpoint.has(state, "c"))
  assertFalse("Does not have d", Fixpoint.has(state, "d"))
}

// ============================================================================
// Test: Multiple Roots
// ============================================================================

let testMultipleRoots = () => {
  Console.log("")
  Console.log("=== Test: Multiple Roots ===")
  
  // Graph: a -> b, c -> d (disconnected components)
  let edges = makeEdges([("a", ["b"]), ("c", ["d"])])
  let config = makeConfig(edges)
  
  let state = Fixpoint.make(~config, ~base=["a", "c"])
  
  assertEqual("Contains both components", Fixpoint.current(state), ["a", "b", "c", "d"])
}

// ============================================================================
// Test: Diamond Graph
// ============================================================================

let testDiamond = () => {
  Console.log("")
  Console.log("=== Test: Diamond Graph ===")
  
  // Graph: a -> b, a -> c, b -> d, c -> d
  let edges = makeEdges([("a", ["b", "c"]), ("b", ["d"]), ("c", ["d"])])
  let config = makeConfig(edges)
  
  let state = Fixpoint.make(~config, ~base=["a"])
  
  assertEqual("Contains all nodes", Fixpoint.current(state), ["a", "b", "c", "d"])
  
  // Check ranks
  switch Fixpoint.rank(state, "a") {
  | Some(r) => assertSize("Rank of a is 0", r, 0)
  | None => assertTrue("Rank of a should exist", false)
  }
  switch Fixpoint.rank(state, "d") {
  | Some(r) => assertSize("Rank of d is 2", r, 2)
  | None => assertTrue("Rank of d should exist", false)
  }
}

// ============================================================================
// Test: Cycle
// ============================================================================

let testCycle = () => {
  Console.log("")
  Console.log("=== Test: Cycle ===")
  
  // Graph: a -> b -> c -> b (cycle from root)
  let edges = makeEdges([("a", ["b"]), ("b", ["c"]), ("c", ["b"])])
  let config = makeConfig(edges)
  
  let state = Fixpoint.make(~config, ~base=["a"])
  
  assertEqual("Contains a, b, c", Fixpoint.current(state), ["a", "b", "c"])
}

// ============================================================================
// Test: Add Base Element
// ============================================================================

let testAddBase = () => {
  Console.log("")
  Console.log("=== Test: Add Base Element ===")
  
  // Graph: a -> b, c -> d
  let edges = makeEdges([("a", ["b"]), ("c", ["d"])])
  let config = makeConfig(edges)
  
  let state = Fixpoint.make(~config, ~base=["a"])
  assertEqual("Initial: a, b", Fixpoint.current(state), ["a", "b"])
  
  let changes = Fixpoint.applyDelta(state, {
    ...Fixpoint.emptyDelta(),
    addedToBase: ["c"],
  })
  
  assertEqual("Added c, d", changes.added, ["c", "d"])
  assertEqual("Nothing removed", changes.removed, [])
  assertEqual("Final: a, b, c, d", Fixpoint.current(state), ["a", "b", "c", "d"])
}

// ============================================================================
// Test: Remove Base Element
// ============================================================================

let testRemoveBase = () => {
  Console.log("")
  Console.log("=== Test: Remove Base Element ===")
  
  // Graph: a -> b -> c
  let edges = makeEdges([("a", ["b"]), ("b", ["c"])])
  let config = makeConfig(edges)
  
  let state = Fixpoint.make(~config, ~base=["a"])
  assertEqual("Initial: a, b, c", Fixpoint.current(state), ["a", "b", "c"])
  
  let changes = Fixpoint.applyDelta(state, {
    ...Fixpoint.emptyDelta(),
    removedFromBase: ["a"],
  })
  
  assertEqual("Nothing added", changes.added, [])
  assertEqual("Removed a, b, c", changes.removed, ["a", "b", "c"])
  assertEqual("Final: empty", Fixpoint.current(state), [])
}

// ============================================================================
// Test: Add Step (Edge)
// ============================================================================

let testAddStep = () => {
  Console.log("")
  Console.log("=== Test: Add Step (Edge) ===")
  
  // Start with just a, then add edge a -> b
  let edges: Map.t<string, Set.t<string>> = Map.make()
  let config = makeConfig(edges)
  
  let state = Fixpoint.make(~config, ~base=["a"])
  assertEqual("Initial: just a", Fixpoint.current(state), ["a"])
  
  // Add the edge a -> b to the edges map
  edges->Map.set("a", Set.fromArray(["b"]))
  
  let changes = Fixpoint.applyDelta(state, {
    ...Fixpoint.emptyDelta(),
    addedToStep: [("a", "b")],
  })
  
  assertEqual("Added b", changes.added, ["b"])
  assertEqual("Final: a, b", Fixpoint.current(state), ["a", "b"])
}

// ============================================================================
// Test: Remove Step (Edge)
// ============================================================================

let testRemoveStep = () => {
  Console.log("")
  Console.log("=== Test: Remove Step (Edge) ===")
  
  // Graph: a -> b -> c, remove a -> b
  let edges = makeEdges([("a", ["b"]), ("b", ["c"])])
  let config = makeConfig(edges)
  
  let state = Fixpoint.make(~config, ~base=["a"])
  assertEqual("Initial: a, b, c", Fixpoint.current(state), ["a", "b", "c"])
  
  // Remove edge a -> b from edges map
  edges->Map.delete("a")->ignore
  
  let changes = Fixpoint.applyDelta(state, {
    ...Fixpoint.emptyDelta(),
    removedFromStep: [("a", "b")],
  })
  
  assertEqual("Nothing added", changes.added, [])
  assertEqual("Removed b, c", changes.removed, ["b", "c"])
  assertEqual("Final: just a", Fixpoint.current(state), ["a"])
}

// ============================================================================
// Test: Cycle Removal (Well-Founded Derivation)
// ============================================================================

let testCycleRemoval = () => {
  Console.log("")
  Console.log("=== Test: Cycle Removal (Well-Founded) ===")
  
  // Graph: a -> b -> c -> b (b-c cycle reachable from a)
  // If we remove a -> b, the cycle should die because neither b nor c
  // has a well-founded deriver (they have equal ranks, can't support each other)
  let edges = makeEdges([("a", ["b"]), ("b", ["c"]), ("c", ["b"])])
  let config = makeConfig(edges)
  
  let state = Fixpoint.make(~config, ~base=["a"])
  assertEqual("Initial: a, b, c", Fixpoint.current(state), ["a", "b", "c"])
  
  // Remove edge a -> b
  edges->Map.set("a", Set.make())
  
  let changes = Fixpoint.applyDelta(state, {
    ...Fixpoint.emptyDelta(),
    removedFromStep: [("a", "b")],
  })
  
  assertEqual("Removed b, c (cycle dies)", changes.removed, ["b", "c"])
  assertEqual("Final: just a", Fixpoint.current(state), ["a"])
}

// ============================================================================
// Test: Alternative Support Keeps Element Alive
// ============================================================================

let testAlternativeSupport = () => {
  Console.log("")
  Console.log("=== Test: Alternative Support ===")
  
  // Graph: a -> b, a -> c -> b
  // If we remove a -> b, b should survive via a -> c -> b
  let edges = makeEdges([("a", ["b", "c"]), ("c", ["b"])])
  let config = makeConfig(edges)
  
  let state = Fixpoint.make(~config, ~base=["a"])
  assertEqual("Initial: a, b, c", Fixpoint.current(state), ["a", "b", "c"])
  
  // Remove direct edge a -> b
  edges->Map.set("a", Set.fromArray(["c"]))
  
  let changes = Fixpoint.applyDelta(state, {
    ...Fixpoint.emptyDelta(),
    removedFromStep: [("a", "b")],
  })
  
  assertEqual("Nothing removed (b still reachable via c)", changes.removed, [])
  assertEqual("Final: a, b, c", Fixpoint.current(state), ["a", "b", "c"])
}

// ============================================================================
// Test: Empty Base
// ============================================================================

let testEmptyBase = () => {
  Console.log("")
  Console.log("=== Test: Empty Base ===")
  
  let edges = makeEdges([("a", ["b"])])
  let config = makeConfig(edges)
  
  let state = Fixpoint.make(~config, ~base=[])
  
  assertEqual("Empty base gives empty fixpoint", Fixpoint.current(state), [])
  assertSize("Size is 0", Fixpoint.size(state), 0)
}

// ============================================================================
// Test: Self Loop
// ============================================================================

let testSelfLoop = () => {
  Console.log("")
  Console.log("=== Test: Self Loop ===")
  
  // Graph: a -> a (self loop)
  let edges = makeEdges([("a", ["a"])])
  let config = makeConfig(edges)
  
  let state = Fixpoint.make(~config, ~base=["a"])
  
  assertEqual("Self loop: just a", Fixpoint.current(state), ["a"])
}

// ============================================================================
// Run all tests
// ============================================================================

let runTests = () => {
  Console.log("Fixpoint Tests")
  Console.log("===============")
  
  testBasicExpansion()
  testMultipleRoots()
  testDiamond()
  testCycle()
  testAddBase()
  testRemoveBase()
  testAddStep()
  testRemoveStep()
  testCycleRemoval()
  testAlternativeSupport()
  testEmptyBase()
  testSelfLoop()
  
  Console.log("")
  Console.log("===============")
  Console.log2("Total:", testCount.contents)
  Console.log2("Passed:", passCount.contents)
  Console.log2("Failed:", failCount.contents)
  
  if failCount.contents > 0 {
    Console.log("")
    Console.log("SOME TESTS FAILED!")
  } else {
    Console.log("")
    Console.log("ALL TESTS PASSED!")
  }
}

runTests()

