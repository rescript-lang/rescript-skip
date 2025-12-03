/**
 * Fixpoint Algorithm Test
 * 
 * This file tests the incremental fixpoint algorithms using the examples
 * from incremental_fixpoint_notes.tex (Section 4: Worked Example: DCE in Detail).
 * 
 * Run with: node examples/FixpointTest.res.js
 */

// ============================================================================
// Test utilities
// ============================================================================

module Map = Belt.Map

let log = msg => Console.log(msg)
let logArray = (label, arr) => Console.log(label ++ ": [" ++ arr->Array.join(", ") ++ "]")

// Test tracking
let passed = ref(0)
let failed = ref(0)
let failures: ref<array<string>> = ref([])

let assertEqual = (actual: 'a, expected: 'a, msg: string) => {
  if actual == expected {
    Console.log("✓ " ++ msg)
    passed := passed.contents + 1
  } else {
    Console.log("✗ " ++ msg)
    Console.log("  Expected: " ++ JSON.stringifyAny(expected)->Option.getOr("?"))
    Console.log("  Actual: " ++ JSON.stringifyAny(actual)->Option.getOr("?"))
    failed := failed.contents + 1
    failures := Array.concat(failures.contents, [msg])
  }
}

let assertArrayEqual = (actual: array<string>, expected: array<string>, msg: string) => {
  let sortedActual = actual->Array.toSorted(String.compare)
  let sortedExpected = expected->Array.toSorted(String.compare)
  assertEqual(sortedActual, sortedExpected, msg)
}

let printSummary = () => {
  let total = passed.contents + failed.contents
  log("\n" ++ String.repeat("=", 60))
  log("TEST SUMMARY")
  log(String.repeat("=", 60))
  log(`Total:  ${Int.toString(total)} tests`)
  log(`Passed: ${Int.toString(passed.contents)} ✓`)
  log(`Failed: ${Int.toString(failed.contents)} ✗`)
  
  if failed.contents > 0 {
    log("\nFailed tests:")
    failures.contents->Array.forEach(f => log("  - " ++ f))
  }
  
  log(String.repeat("=", 60))
  if failed.contents == 0 {
    log("All tests passed! 🎉")
  } else {
    log(`${Int.toString(failed.contents)} test(s) failed.`)
  }
}

// ============================================================================
// Test: Initial Graph (from Section 4.1)
// ============================================================================

/**
 * Initial graph:
 * 
 *   R → A → B → C
 *       ↓   ↑
 *       D ──┘
 * 
 * base = {R}
 * stepFwd(R) = {A}
 * stepFwd(A) = {B, D}
 * stepFwd(B) = {C}
 * stepFwd(D) = {B}
 * 
 * Expected fixpoint: {R, A, B, C, D}
 * Expected ranks: R:0, A:1, B:2, C:3, D:2
 */
let testInitialGraph = () => {
  log("\n=== Test: Initial Graph ===")

  let edges = Map.String.fromArray([
    ("R", ["A"]),
    ("A", ["B", "D"]),
    ("B", ["C"]),
    ("D", ["B"]),
  ])

  let config: Fixpoint.config<string> = {
    stepFwd: x => edges->Map.String.getWithDefault(x, []),
  }

  let state = Fixpoint.make(~config, ~base=["R"])

  // Check fixpoint
  assertArrayEqual(Fixpoint.current(state), ["R", "A", "B", "C", "D"], "Initial fixpoint contains R, A, B, C, D")

  // Check ranks
  assertEqual(Fixpoint.rank(state, "R"), Some(0), "R has rank 0")
  assertEqual(Fixpoint.rank(state, "A"), Some(1), "A has rank 1")
  assertEqual(Fixpoint.rank(state, "B"), Some(2), "B has rank 2")
  assertEqual(Fixpoint.rank(state, "C"), Some(3), "C has rank 3")
  assertEqual(Fixpoint.rank(state, "D"), Some(2), "D has rank 2")

  state
}

// ============================================================================
// Test: Expansion - Adding Edge R → E (from Section 4.2)
// ============================================================================

/**
 * Add edge R → E where E → F
 * 
 *   R → A → B → C
 *   ↓   ↓   ↑
 *   E   D ──┘
 *   ↓
 *   F
 * 
 * Expected: E and F are added with ranks 1 and 2
 */
let testExpansion = () => {
  log("\n=== Test: Expansion (Add Edge) ===")

  // Start with extended edges including E → F
  let edges = Map.String.fromArray([
    ("R", ["A", "E"]),
    ("A", ["B", "D"]),
    ("B", ["C"]),
    ("D", ["B"]),
    ("E", ["F"]),
  ])

  let config: Fixpoint.config<string> = {
    stepFwd: x => edges->Map.String.getWithDefault(x, []),
  }

  // Start with original graph (without R → E)
  let originalEdges = Map.String.fromArray([
    ("R", ["A"]),
    ("A", ["B", "D"]),
    ("B", ["C"]),
    ("D", ["B"]),
  ])

  let originalConfig: Fixpoint.config<string> = {
    stepFwd: x => originalEdges->Map.String.getWithDefault(x, []),
  }

  let state = Fixpoint.make(~config=originalConfig, ~base=["R"])
  assertArrayEqual(Fixpoint.current(state), ["R", "A", "B", "C", "D"], "Before expansion: R, A, B, C, D")

  // Now simulate adding edge R → E by applying delta
  // We need to update the config's stepFwd - but since it's a function,
  // we'll recreate with the new edges
  let newState = Fixpoint.make(~config, ~base=["R"])

  assertArrayEqual(
    Fixpoint.current(newState),
    ["R", "A", "B", "C", "D", "E", "F"],
    "After expansion: R, A, B, C, D, E, F",
  )
  assertEqual(Fixpoint.rank(newState, "E"), Some(1), "E has rank 1")
  assertEqual(Fixpoint.rank(newState, "F"), Some(2), "F has rank 2")
}

// ============================================================================
// Test: Contraction - Removing Edge A → D (from Section 4.3)
// ============================================================================

/**
 * Remove edge A → D
 * 
 *   R → A → B → C
 *           ↑
 *       D ──┘  (D unreachable now)
 * 
 * Expected: D is removed (no well-founded deriver)
 */
let testContraction = () => {
  log("\n=== Test: Contraction (Remove Edge) ===")

  // Full edges
  let fullEdges = Map.String.fromArray([
    ("R", ["A"]),
    ("A", ["B", "D"]),
    ("B", ["C"]),
    ("D", ["B"]),
  ])

  let fullConfig: Fixpoint.config<string> = {
    stepFwd: x => fullEdges->Map.String.getWithDefault(x, []),
  }

  let state = Fixpoint.make(~config=fullConfig, ~base=["R"])
  assertArrayEqual(Fixpoint.current(state), ["R", "A", "B", "C", "D"], "Before contraction: R, A, B, C, D")

  // Apply delta: remove derivation A → D
  let changes = Fixpoint.applyDelta(
    state,
    {
      ...Fixpoint.emptyDelta,
      removedFromStep: [("A", "D")],
    },
  )

  logArray("Removed elements", changes.removed)
  assertArrayEqual(changes.removed, ["D"], "D was removed")
  assertArrayEqual(Fixpoint.current(state), ["R", "A", "B", "C"], "After contraction: R, A, B, C")
}

// ============================================================================
// Test: Contraction with Cycles (from Section 4.4)
// ============================================================================

/**
 * Graph with cycle:
 * 
 *   R → A ↔ B
 * 
 * ranks: R:0, A:1, B:2
 * 
 * Remove edge R → A:
 * - A loses its wf-deriver (R)
 * - B has A as deriver, but rank[A] = 1 > rank[A] is false... wait
 * - Actually: B is derived by A. A's rank is 1, B's rank is 2.
 * - When A dies, B loses its only wf-deriver
 * - B cannot use A as deriver (A is dying)
 * - B → A edge doesn't help because rank[B] = 2 > rank[A] = 1
 * 
 * Expected: A and B both removed, only R remains
 */
let testCycleContraction = () => {
  log("\n=== Test: Cycle Contraction ===")

  // Graph with cycle
  let edges = Map.String.fromArray([("R", ["A"]), ("A", ["B"]), ("B", ["A"])])

  let config: Fixpoint.config<string> = {
    stepFwd: x => edges->Map.String.getWithDefault(x, []),
  }

  let state = Fixpoint.make(~config, ~base=["R"])
  assertArrayEqual(Fixpoint.current(state), ["R", "A", "B"], "Before: R, A, B in fixpoint")
  assertEqual(Fixpoint.rank(state, "R"), Some(0), "R has rank 0")
  assertEqual(Fixpoint.rank(state, "A"), Some(1), "A has rank 1")
  assertEqual(Fixpoint.rank(state, "B"), Some(2), "B has rank 2")

  // Remove derivation R → A
  let changes = Fixpoint.applyDelta(
    state,
    {
      ...Fixpoint.emptyDelta,
      removedFromStep: [("R", "A")],
    },
  )

  logArray("Removed elements", changes.removed)
  // Both A and B should be removed
  assertArrayEqual(changes.removed->Array.toSorted(String.compare), ["A", "B"], "A and B were removed (cycle broken)")
  assertArrayEqual(Fixpoint.current(state), ["R"], "After: only R remains")
}

// ============================================================================
// Test: Remove from Base
// ============================================================================

let testRemoveFromBase = () => {
  log("\n=== Test: Remove from Base ===")

  let edges = Map.String.fromArray([("R", ["A"]), ("A", ["B"])])

  let config: Fixpoint.config<string> = {
    stepFwd: x => edges->Map.String.getWithDefault(x, []),
  }

  let state = Fixpoint.make(~config, ~base=["R"])
  assertArrayEqual(Fixpoint.current(state), ["R", "A", "B"], "Before: R, A, B in fixpoint")

  // Remove R from base
  let changes = Fixpoint.applyDelta(
    state,
    {
      ...Fixpoint.emptyDelta,
      removedFromBase: ["R"],
    },
  )

  logArray("Removed elements", changes.removed)
  assertArrayEqual(
    changes.removed->Array.toSorted(String.compare),
    ["A", "B", "R"],
    "All elements removed when root is removed",
  )
  assertArrayEqual(Fixpoint.current(state), [], "After: empty fixpoint")
}

// ============================================================================
// Test: Add to Base
// ============================================================================

let testAddToBase = () => {
  log("\n=== Test: Add to Base ===")

  let edges = Map.String.fromArray([("R", ["A"]), ("A", ["B"]), ("S", ["C"]), ("C", ["D"])])

  let config: Fixpoint.config<string> = {
    stepFwd: x => edges->Map.String.getWithDefault(x, []),
  }

  // Start with only R as base
  let state = Fixpoint.make(~config, ~base=["R"])
  assertArrayEqual(Fixpoint.current(state), ["R", "A", "B"], "Before: R, A, B in fixpoint")

  // Add S to base
  let changes = Fixpoint.applyDelta(
    state,
    {
      ...Fixpoint.emptyDelta,
      addedToBase: ["S"],
    },
  )

  logArray("Added elements", changes.added)
  assertArrayEqual(
    changes.added->Array.toSorted(String.compare),
    ["C", "D", "S"],
    "S, C, D added",
  )
  assertArrayEqual(
    Fixpoint.current(state)->Array.toSorted(String.compare),
    ["A", "B", "C", "D", "R", "S"],
    "After: R, A, B, S, C, D in fixpoint",
  )
}

// ============================================================================
// Test: Multiple Paths (Diamond)
// ============================================================================

let testDiamond = () => {
  log("\n=== Test: Diamond (Multiple Paths) ===")

  // Diamond: R → A → C, R → B → C
  let edges = Map.String.fromArray([("R", ["A", "B"]), ("A", ["C"]), ("B", ["C"])])

  let config: Fixpoint.config<string> = {
    stepFwd: x => edges->Map.String.getWithDefault(x, []),
  }

  let state = Fixpoint.make(~config, ~base=["R"])
  assertArrayEqual(Fixpoint.current(state), ["R", "A", "B", "C"], "Initial: R, A, B, C")
  assertEqual(Fixpoint.rank(state, "C"), Some(2), "C has rank 2 (shortest path)")

  // Remove derivation A → C (C still reachable via B)
  let changes = Fixpoint.applyDelta(
    state,
    {
      ...Fixpoint.emptyDelta,
      removedFromStep: [("A", "C")],
    },
  )

  assertArrayEqual(changes.removed, [], "No elements removed (C still reachable via B)")
  assertArrayEqual(Fixpoint.current(state), ["R", "A", "B", "C"], "After: still R, A, B, C")

  // Now remove derivation B → C (C becomes unreachable)
  let changes2 = Fixpoint.applyDelta(
    state,
    {
      ...Fixpoint.emptyDelta,
      removedFromStep: [("B", "C")],
    },
  )

  assertArrayEqual(changes2.removed, ["C"], "C removed (no more paths)")
  assertArrayEqual(Fixpoint.current(state), ["R", "A", "B"], "After: R, A, B")
}

// ============================================================================
// Run all tests
// ============================================================================

let main = () => {
  log("Fixpoint Algorithm Tests")
  log("========================")

  let _ = testInitialGraph()
  testExpansion()
  testContraction()
  testCycleContraction()
  testRemoveFromBase()
  testAddToBase()
  testDiamond()

  printSummary()
}

main()

