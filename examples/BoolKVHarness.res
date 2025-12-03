// Harness to inspect how booleans appear as keys and values via the Skip API.

module Server = {
  @module("./BoolKVService.js")
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
}

let logBoolKV = (entries: array<(JSON.t, array<JSON.t>)>) => {
  let rows =
    entries->Array.map(((k, vals)) =>
      switch vals {
      | [v] =>
        (
          JSON.stringify(k),
          typeof(k),
          JSON.stringify(v),
          typeof(v),
        )
      | _ => ("<unexpected>", typeof(k), "<unexpected>", typeof(k))
      }
    )
  Console.log2("boolKV snapshot", rows)
}

let run = async () => {
  Console.log("bool-kv: starting BoolKVService on 18092/18093…")
  let server = await Server.start(Server.defaultOpts)
  Console.log("bool-kv: service started")

  let broker = Client.makeBroker(Server.defaultOpts)

  let entries = await SkipruntimeHelpers.getAll(broker, "boolKV", JSON.Null)
  logBoolKV(entries)

  await Server.stop(server)
  Console.log("bool-kv: service closed")
}

let () = run()->ignore

