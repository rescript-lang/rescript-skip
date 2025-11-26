module Server = {
  @module("./LiveService.mjs")
  external service: SkipruntimeCore.skipService = "service"

  let start = (opts: SkipruntimeServer.runOptions) =>
    SkipruntimeServer.Natural.runService(service, ~options=opts)
  let stop = (server: SkipruntimeServer.skipServer) =>
    SkipruntimeServer.Natural.close(server)
}

module Client = {
  let localhost = "127.0.0.1"

  // Broker for talking to the running service over HTTP/SSE.
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

  let logSnapshot = async (broker, label) => {
    let snapshot = await SkipruntimeHelpers.getAll(broker, "echo", JSON.Null)
    Console.log2(label, snapshot)
  }

  let updateInput = (broker, entries) =>
    SkipruntimeHelpers.update(broker, "input", entries)

  // Subscribe once and read the first SSE chunk to prove live updates.
  let readOneSse = async (opts: SkipruntimeServer.runOptions, broker) => {
    let uuid = await SkipruntimeHelpers.getStreamUUID(broker, "echo", JSON.Null)
    let streamUrl =
      `http://${localhost}:${opts.streaming_port->Int.toString}/v1/streams/${uuid}`
    Console.log2("live client: subscribing to", streamUrl)
    let ssePromise = SkipruntimeCore.Context.readFirstSSE(streamUrl)
    await updateInput(
      broker,
      [(JSON.String("sse"), [JSON.String("ping")])],
    )
    await ssePromise
  }
}

let run = async () => {
  let opts: SkipruntimeServer.runOptions = {
    streaming_port: 18081,
    control_port: 18080,
    platform: Some(#wasm),
    no_cors: None,
  }

  Console.log("server: starting wasm service on ports 18080/18081…")
  let server = await Server.start(opts)
  Console.log("server: service started")

  let broker = Client.makeBroker(opts)

  await Client.logSnapshot(broker, "live client: initial getAll")

  await Client.updateInput(
    broker,
    [
      (JSON.String("foo"), [JSON.String("baz")]),
      (JSON.String("bar"), [JSON.String("qux")]),
    ],
  )
  await Client.logSnapshot(broker, "live client: after update getAll")

  let sseChunk = await Client.readOneSse(opts, broker)
  Console.log2("live client: SSE chunk", sseChunk)

  await Server.stop(server)
  Console.log("server: service closed")
}

let () = run()->ignore
