// Reusable harness around a mapper/reducer-driven service.
// Purpose: show reactive snapshot/update flow across derived resources without duplicating the LiveClient SSE demo.

module Server = {
  @module("./LiveHarnessService.js")
  external service: SkipruntimeCore.skipService = "service"
  @module("./LiveHarnessService.js")
  external resetRunStats: unit => unit = "resetRunStats"
  @module("./LiveHarnessService.js")
  external getRunStats: unit => JSON.t = "getRunStats"

  let defaultOpts: SkipruntimeServer.runOptions = {
    streaming_port: 18081,
    control_port: 18080,
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

  let snapshot = async (broker, resource, label) => {
    let snapshot = await SkipruntimeHelpers.getAll(broker, resource, JSON.Null)
    Console.log2(label, snapshot)
  }

  let updateInput = (broker, entries) =>
    SkipruntimeHelpers.update(broker, "numbers", entries)

  let updateEdges = (broker, entries) =>
    SkipruntimeHelpers.update(broker, "edges", entries)

  let getStreamUrl = async (opts: SkipruntimeServer.runOptions, broker, resource) => {
    let uuid = await SkipruntimeHelpers.getStreamUUID(broker, resource, None)
    `http://${localhost}:${opts.streaming_port->Int.toString}/v1/streams/${uuid}`
  }
}

// Client-side O(1) incremental sum.
// Subscribes to SSE stream and applies updates as they arrive.
module ClientSum = {
  type state = {
    mutable total: float,
    mutable numbers: Dict.t<float>,
    mutable subscription: option<SkipruntimeCore.sseSubscription>,
  }

  let state: state = {
    total: 0.,
    numbers: Dict.make(),
    subscription: None,
  }

  // O(1) update: subtract old value, add new value.
  let applyUpdate = (key: string, newValue: float) => {
    let oldValue = state.numbers->Dict.get(key)->Option.getOr(0.)
    state.total = state.total -. oldValue +. newValue
    state.numbers->Dict.set(key, newValue)
  }

  // Parse SSE data: array of [key, [values]] entries.
  // Apply each entry to update the local sum.
  let handleSSEData = (data: JSON.t) => {
    switch data {
    | Array(entries) =>
      entries->Array.forEach(entry => {
        switch entry {
        | Array([String(key), Array(values)]) =>
          // Take first value if present
          switch values[0] {
          | Some(Number(v)) => applyUpdate(key, v)
          | _ => ()
          }
        | _ => ()
        }
      })
    | _ => ()
    }
  }

  let subscribe = (streamUrl: string) => {
    let sub = SkipruntimeCore.subscribeSSE(streamUrl, handleSSEData)
    state.subscription = Some(sub)
  }

  let close = () => {
    switch state.subscription {
    | Some(sub) =>
      sub.close()
      state.subscription = None
    | None => ()
    }
  }

  let getTotal = () => state.total
}

// Small delay to let SSE events propagate.
let delay = ms => {
  Promise.make((resolve, _reject) => {
    let _ = setTimeout(() => resolve(), ms)
  })
}

let run = async () => {
  Console.log("harness: starting LiveService (wasm) on 18080/18081…")
  let server = await Server.start(Server.defaultOpts)
  Console.log("harness: service started")

  let broker = Client.makeBroker(Server.defaultOpts)

  // Subscribe to numbers via SSE - this initializes ClientSum from the stream.
  let streamUrl = await Client.getStreamUrl(Server.defaultOpts, broker, "numbers")
  Console.log2("harness: subscribing to SSE stream", streamUrl)
  ClientSum.subscribe(streamUrl)

  // Wait for initial SSE data to arrive.
  await delay(100)
  Console.log2("harness: client sum (from SSE)", ClientSum.getTotal())

  // Phase 1: Initial snapshot.
  Server.resetRunStats()
  await Client.snapshot(broker, "numbers", "harness: numbers")
  await Client.snapshot(broker, "doubled", "harness: doubled")
  await Client.snapshot(broker, "sum", "harness: sum")
  await Client.snapshot(broker, "dead", "harness: dead code (unreachable nodes)")
  Console.log2("harness: counters after initial snapshot", Server.getRunStats())

  // Phase 2: Update c from 3 to 5.
  await Client.updateInput(broker, [(JSON.String("c"), [JSON.Number(5.)])])
  await Client.snapshot(broker, "numbers", "harness: numbers after c→5")
  await Client.snapshot(broker, "doubled", "harness: doubled after c→5")
  await Client.snapshot(broker, "sum", "harness: sum after c→5")
  await Client.snapshot(broker, "dead", "harness: dead code after c→5 (unchanged)")
  Console.log2("harness: client sum after c→5 (from SSE)", ClientSum.getTotal())
  Console.log2("harness: counters after c→5", Server.getRunStats())

  // Phase 3: Remove an edge to create dead code.
  await Client.updateEdges(broker, [
    (
      JSON.String("fileA"),
      [
        // drop util -> lib edge to make lib/helper unreachable
        JSON.Array([JSON.String("main"), JSON.String("util")]),
      ],
    ),
  ])
  await Client.snapshot(broker, "dead", "harness: dead code after dropping util→lib")

  ClientSum.close()
  await Server.stop(server)
  Console.log("harness: service closed")
}

let () = run()->ignore
