// Harness to exercise Json keys and ordering via the JsonOrderingService.

module Server = {
  @module("./JsonOrderingService.js")
  external service: SkipruntimeCore.skipService = "service"

  let defaultOpts: SkipruntimeServer.runOptions = {
    streaming_port: 18091,
    control_port: 18090,
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
}

// Pretty-print just the keys of a snapshot, using JSON.stringify for clarity.
// We also log the JS typeof for debugging the runtime's ordering.
let logKeys = (
  label: string,
  entries: array<(JSON.t, array<JSON.t>)>,
) => {
  let keys =
    entries->Array.map(((k, _vals)) => (JSON.stringify(k), typeof(k) :> string))
  Console.log2(label, keys)
}

// FINDINGS about the Skip runtime's JSON handling (discovered by running this harness):
//
// 1. SERIALIZATION: Booleans are converted to numbers in output: false -> 0, true -> 1
//    This conversion happens recursively in arrays and objects.
//    JS typeof is "number", JSON.stringify shows "0"/"1".
//
// 2. NO KEY COLLISION: Despite the output conversion, boolean keys do NOT collide
//    with numeric 0/1 keys. The runtime preserves their identity internally.
//    Both `false` and `0` can coexist as separate keys (though both serialize as "0").
//    Same for `true` and `1`, and for nested cases like [false] vs [0], {x:false} vs {x:0}.
//
// 3. ORDER: null < booleans (as 0,1) < negative numbers < non-negative numbers < strings < arrays < objects
//    - Booleans-converted-to-numbers come BEFORE all actual numbers (even negatives)
//    - Example: 0(bool) < 1(bool) < -100 < -1 < -0.5 < 0(num) < 0.5 < 1(num) < 1.5 < 100
//    - Strings: lexicographic ("" < "0" < "1" < "a" < "b")
//    - Arrays: lexicographic by elements; [] < [0](bool) < [1](bool) < [-1] < [0](num) < ...
//    - Objects: lexicographic by (key, value) pairs
//
// 4. Nested booleans in arrays/objects are also converted in output:
//    [false] -> [0], {x: true} -> {x: 1}
//    But they remain distinct keys from [0] and {x: 1} (no collision).

// Log keys with their values to see which entry is which
let logKeysWithValues = (
  label: string,
  entries: array<(JSON.t, array<JSON.t>)>,
) => {
  Console.log(label)
  entries->Array.forEach(((k, vals)) => {
    let valStr = switch vals {
    | [v] => JSON.stringify(v)
    | _ => `[${vals->Array.map(v => JSON.stringify(v))->Array.join(", ")}]`
    }
    Console.log2(`  ${JSON.stringify(k)} (${typeof(k) :> string})`, `=> ${valStr}`)
  })
}

let run = async () => {
  Console.log("json-ordering: starting JsonOrderingService on 18090/18091…")
  let server = await Server.start(Server.defaultOpts)
  Console.log("json-ordering: service started")

  let broker = Client.makeBroker(Server.defaultOpts)

  // Inspect initial key order (without top-level null).
  let allKeys = await SkipruntimeHelpers.getAll(broker, "allKeys", JSON.Null)
  logKeysWithValues("json-ordering: allKeys initial", allKeys)

  // Insert a top-level null key via HTTP update and re-check ordering.
  await SkipruntimeHelpers.update(
    broker,
    "allKeys",
    [(JSON.Null, [JSON.String("null-top")])],
  )
  let allKeysWithNull =
    await SkipruntimeHelpers.getAll(broker, "allKeys", JSON.Null)
  logKeysWithValues("json-ordering: allKeys with null", allKeysWithNull)

  // Exercise slice/slices/take/merge and log their key sets for manual inspection.
  let slice = await SkipruntimeHelpers.getAll(broker, "allKeysSlice", JSON.Null)
  logKeys("json-ordering: allKeysSlice", slice)

  let take = await SkipruntimeHelpers.getAll(broker, "allKeysTake", JSON.Null)
  logKeys("json-ordering: allKeysTake", take)

  let slices = await SkipruntimeHelpers.getAll(broker, "allKeysSlices", JSON.Null)
  logKeys("json-ordering: allKeysSlices", slices)

  let merged = await SkipruntimeHelpers.getAll(broker, "mergedKeys", JSON.Null)
  logKeys("json-ordering: mergedKeys", merged)

  await Server.stop(server)
  Console.log("json-ordering: service closed")
}

let () = run()->ignore
