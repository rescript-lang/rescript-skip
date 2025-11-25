open SkipruntimeCore

@module("./LiveService.mjs") external service: skipService = "service"

let run = async () => {
  let opts: SkipruntimeServer.runOptions = {
    streaming_port: 0,
    control_port: 0,
    platform: Some(#wasm),
    no_cors: None,
  }
  Console.log("live test: starting wasm service on ephemeral ports…")
  try {
    let server = await SkipruntimeServer.Natural.runService(service, ~options=opts)
    Console.log("live test: service started")
    await SkipruntimeServer.Natural.close(server)
    Console.log("live test: service closed")
  } catch {
  | err => Console.error2("live test: failed to start service (check for port permissions)", err)
  }
}

let () = run()->ignore
