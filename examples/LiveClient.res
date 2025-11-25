open SkipruntimeCore

@module("./LiveService.mjs") external service: skipService = "service"
@module("../bindings/SkipruntimeCoreHelpers.mjs")
external readFirstSSE: string => promise<string> = "readFirstSSE"

let run = async () => {
  let opts: SkipruntimeServer.runOptions = {
    streaming_port: 18081,
    control_port: 18080,
    platform: Some(#wasm),
    no_cors: None,
  }

  Console.log("live client: starting wasm service on ports 18080/18081…")
  let server = await SkipruntimeServer.Natural.runService(service, ~options=opts)
  Console.log("live client: service started")

  let broker =
    SkipruntimeHelpers.make(
      {
        host: "127.0.0.1",
        streaming_port: opts.streaming_port,
        control_port: opts.control_port,
        secured: None,
      },
      None,
    )

  let before = await SkipruntimeHelpers.getAll(broker, "echo", JSON.Null)
  Console.log2("live client: initial getAll", before)

  await SkipruntimeHelpers.update(
    broker,
    "input",
    [
      (JSON.String("foo"), [JSON.String("baz")]),
      (JSON.String("bar"), [JSON.String("qux")]),
    ],
  )
  let after = await SkipruntimeHelpers.getAll(broker, "echo", JSON.Null)
  Console.log2("live client: after update getAll", after)

  // SSE subscription: read first event from the echo stream
  let uuid = await SkipruntimeHelpers.getStreamUUID(broker, "echo", JSON.Null)
  let streamUrl =
    `http://127.0.0.1:${opts.streaming_port->Int.toString}/v1/streams/${uuid}`
  Console.log2("live client: subscribing to", streamUrl)
  let ssePromise = readFirstSSE(streamUrl)

  await SkipruntimeHelpers.update(
    broker,
    "input",
    [(JSON.String("sse"), [JSON.String("ping")])],
  )
  let sseChunk = await ssePromise
  Console.log2("live client: SSE chunk", sseChunk)

  await SkipruntimeServer.Natural.close(server)
  Console.log("live client: service closed")
}

let () = run()->ignore
