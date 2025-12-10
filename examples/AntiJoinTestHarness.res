/**
 * AntiJoinTestHarness - Tests if Skip tracks dependencies on missing keys
 * 
 * This is a critical test for understanding Skip's expressivity.
 * 
 * The question: Can anti-join (set difference) be expressed via map-with-lookup?
 * 
 * Test sequence:
 * 1. left = {a, b}, right = {} → antiJoin should be {a, b}
 * 2. Add a to right → antiJoin should become {b} (a now blocked)
 * 3. Remove a from right → antiJoin should become {a, b} again
 * 
 * If this works, Skip DOES track negative dependencies, and the paper's claim
 * that anti-join is inexpressible needs revision!
 * 
 * Run with: node examples/AntiJoinTestHarness.res.js
 */

module Server = {
  @module("./AntiJoinTestService.js")
  external service: SkipruntimeCore.skipService = "service"

  let defaultOpts: SkipruntimeServer.runOptions = {
    streaming_port: 18093,
    control_port: 18092,
    platform: Some(#wasm),
    no_cors: None,
  }

  let start = (opts: SkipruntimeServer.runOptions) =>
    SkipruntimeServer.Natural.runService(service, ~options=opts)

  let stop = (server: SkipruntimeServer.skipServer) =>
    SkipruntimeServer.Natural.close(server)
}

module Client = {
  let localhost = "127.0.0.1"

  let makeBroker = (opts: SkipruntimeServer.runOptions) =>
    SkipruntimeHelpers.make(
      Some({
        host: localhost,
        streaming_port: opts.streaming_port,
        control_port: opts.control_port,
        secured: None,
      }),
      None,
    )

  // Add a blocker to the right collection
  let addBlocker = (broker, key: string, reason: string) => {
    let data = JSON.Object(Dict.fromArray([
      ("reason", JSON.String(reason)),
    ]))
    SkipruntimeHelpers.update(broker, "right", [
      (JSON.String(key), [data])
    ])
  }

  // Remove a blocker from the right collection
  let removeBlocker = (broker, key: string) => {
    SkipruntimeHelpers.update(broker, "right", [
      (JSON.String(key), [])  // Empty = delete
    ])
  }

  let getStreamUrl = async (opts: SkipruntimeServer.runOptions, broker, resource) => {
    let uuid = await SkipruntimeHelpers.getStreamUUID(broker, resource, None)
    `http://${localhost}:${opts.streaming_port->Int.toString}/v1/streams/${uuid}`
  }
}

// Track SSE updates
let sseUpdates: ref<array<string>> = ref([])
let updateCount = ref(0)

let handleSSE = (data: JSON.t) => {
  updateCount := updateCount.contents + 1
  let dataStr = JSON.stringify(data)
  sseUpdates.contents->Array.push(dataStr)->ignore
  Console.log(`[SSE #${updateCount.contents->Int.toString}] ${dataStr}`)
}

let delay = ms => {
  Promise.make((resolve, _reject) => {
    let _ = setTimeout(() => resolve(), ms)
  })
}

let run = async () => {
  Console.log("===========================================")
  Console.log("Anti-Join Test: Does Skip Track Negative Dependencies?")
  Console.log("===========================================")
  Console.log("")
  Console.log("Question: Can we express anti-join (set difference) via map-with-lookup?")
  Console.log("")
  Console.log("Test: left={a,b}, right={}. Mapper outputs left entries NOT in right.")
  Console.log("When we add 'a' to right, does 'a' disappear from the anti-join output?")
  Console.log("")

  let server = await Server.start(Server.defaultOpts)
  Console.log("Server started on ports 18092/18093")

  let broker = Client.makeBroker(Server.defaultOpts)

  // Subscribe to the antiJoin resource
  let antiJoinUrl = await Client.getStreamUrl(Server.defaultOpts, broker, "antiJoin")
  Console.log(`Subscribing to antiJoin resource...`)
  let subscription = SkipruntimeCore.subscribeSSE(antiJoinUrl, handleSSE)

  await delay(500)

  // Phase 1: Initial state
  Console.log("")
  Console.log("--- Phase 1: Initial State ---")
  Console.log("  left = {a: value_a, b: value_b}")
  Console.log("  right = {} (empty)")
  Console.log("  Expected antiJoin: {a, b} (nothing blocked)")
  Console.log("")

  await delay(300)

  // Phase 2: Add blocker for 'a'
  Console.log("--- Phase 2: Add blocker for 'a' ---")
  Console.log("  Adding right[a] = {reason: 'blocked'}")
  Console.log("")
  Console.log("  ⚡ CRITICAL TEST: Does Skip detect that antiJoin[a] should update?")
  Console.log("  If yes → Skip tracks negative dependencies → anti-join IS expressible!")
  Console.log("  If no → Skip doesn't track missing-key lookups → anti-join needs new operator")
  Console.log("")

  await Client.addBlocker(broker, "a", "blocked")
  
  await delay(500)

  // Phase 3: Remove blocker for 'a'
  Console.log("")
  Console.log("--- Phase 3: Remove blocker for 'a' ---")
  Console.log("  Removing right[a]")
  Console.log("  Expected: antiJoin should have {a, b} again")
  Console.log("")

  await Client.removeBlocker(broker, "a")
  
  await delay(500)

  // Summary
  Console.log("")
  Console.log("===========================================")
  Console.log("RESULTS")
  Console.log("===========================================")
  Console.log(`Total SSE updates received: ${updateCount.contents->Int.toString}`)
  Console.log("")
  
  if updateCount.contents >= 3 {
    Console.log("✅ PASS: Skip DOES track negative dependencies!")
    Console.log("   Anti-join IS expressible via map-with-lookup.")
    Console.log("   The paper's claim needs revision.")
  } else if updateCount.contents == 1 {
    Console.log("❌ FAIL: Skip does NOT track negative dependencies.")
    Console.log("   Only received initial state, no updates when right changed.")
    Console.log("   Anti-join requires a new operator (filterNotMatchingOn).")
  } else {
    Console.log("⚠️  INCONCLUSIVE: Received ${updateCount.contents->Int.toString} updates.")
    Console.log("   Check the SSE output above to understand what happened.")
  }
  Console.log("")

  // Cleanup
  subscription.close()
  await Server.stop(server)
  Console.log("Server stopped.")
  Console.log("")
  Console.log("Test complete!")
}

let () = run()->ignore

