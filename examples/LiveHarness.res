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
      {
        host: localhost,
        streaming_port: opts.streaming_port,
        control_port: opts.control_port,
        secured: None,
      },
      None,
    )

  let snapshot = async (broker, resource, label) => {
    let snapshot = await SkipruntimeHelpers.getAll(broker, resource, JSON.Null)
    Console.log2(label, snapshot)
  }

  let updateInput = (broker, entries) =>
    SkipruntimeHelpers.update(broker, "numbers", entries)
}

// Client-side O(1) incremental sum.
// Demonstrates how to layer efficient aggregates on top of reactive data.
module ClientSum = {
  type state = {
    mutable total: float,
    mutable numbers: Dict.t<float>,
  }

  let state: state = {
    total: 0.,
    numbers: Dict.make(),
  }

  let init = () => {
    // Must stay in sync with LiveHarnessService.initialData.numbers
    let initialNumbers = [
      ("a", 1.),
      ("b", 2.),
      ("c", 3.),
      ("d", 4.),
      ("e", 5.),
      ("f", 6.),
      ("g", 7.),
      ("h", 8.),
      ("i", 9.),
      ("j", 10.),
    ]

    let numbers = Dict.fromArray(initialNumbers)
    let total = initialNumbers->Array.reduce(0., (acc, (_k, v)) => acc +. v)

    state.total = total
    state.numbers = numbers
  }

  // O(1) update: subtract old value, add new value.
  let applyUpdate = (key: string, newValue: float) => {
    let oldValue = state.numbers->Dict.get(key)->Option.getOr(0.)
    state.total = state.total -. oldValue +. newValue
    state.numbers->Dict.set(key, newValue)
  }
}

let run = async () => {
  Console.log("harness: starting LiveService (wasm) on 18080/18081…")
  let server = await Server.start(Server.defaultOpts)
  Console.log("harness: service started")

  let broker = Client.makeBroker(Server.defaultOpts)

  // Initialize client-side sum.
  ClientSum.init()
  Console.log2("harness: client sum (initial)", ClientSum.state.total)

  // Phase 1: Initial snapshot.
  Server.resetRunStats()
  await Client.snapshot(broker, "numbers", "harness: numbers")
  await Client.snapshot(broker, "doubled", "harness: doubled")
  await Client.snapshot(broker, "sum", "harness: sum")
  Console.log2("harness: counters after initial snapshot", Server.getRunStats())

  // Phase 2: Update c from 3 to 5.
  await Client.updateInput(broker, [(JSON.String("c"), [JSON.Number(5.)])])
  await Client.snapshot(broker, "numbers", "harness: numbers after c→5")
  await Client.snapshot(broker, "doubled", "harness: doubled after c→5")
  await Client.snapshot(broker, "sum", "harness: sum after c→5")
  ClientSum.applyUpdate("c", 5.)
  Console.log2("harness: client sum after c→5", ClientSum.state.total)
  Console.log2("harness: counters after c→5", Server.getRunStats())

  await Server.stop(server)
  Console.log("harness: service closed")
}

let () = run()->ignore
