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

let run = async () => {
  Console.log("harness: starting LiveService (wasm) on 18080/18081…")
  let server = await Server.start(Server.defaultOpts)
  Console.log("harness: service started")

  let broker = Client.makeBroker(Server.defaultOpts)

  Server.resetRunStats()
  await Client.snapshot(broker, "numbers", "harness: initial numbers")
  await Client.snapshot(broker, "doubled", "harness: initial doubled")
  await Client.snapshot(broker, "sumNaive", "harness: initial sum (naive)")
  Console.log2("harness: run counters (naive initial)", Server.getRunStats())

  await Client.updateInput(
    broker,
    [
      (JSON.String("c"), [JSON.Number(5.)]),
    ],
  )
  await Client.snapshot(broker, "numbers", "harness: numbers after update")
  await Client.snapshot(broker, "doubled", "harness: doubled after update")
  await Client.snapshot(broker, "sumNaive", "harness: sum (naive) after update")
  Console.log2("harness: run counters (naive after update)", Server.getRunStats())

  Server.resetRunStats()
  await Client.snapshot(broker, "numbers", "harness: initial numbers (inc)")
  await Client.snapshot(broker, "doubled", "harness: initial doubled (inc)")
  await Client.snapshot(broker, "sumInc", "harness: initial sum (inc)")
  Console.log2("harness: run counters (inc initial)", Server.getRunStats())

  await Client.updateInput(
    broker,
    [
      (JSON.String("d"), [JSON.Number(7.)]),
    ],
  )
  await Client.snapshot(broker, "numbers", "harness: numbers after update (inc)")
  await Client.snapshot(broker, "doubled", "harness: doubled after update (inc)")
  await Client.snapshot(broker, "sumInc", "harness: sum (inc) after update")
  Console.log2("harness: run counters (inc after update)", Server.getRunStats())

  await Server.stop(server)
  Console.log("harness: service closed")
}

let () = run()->ignore
