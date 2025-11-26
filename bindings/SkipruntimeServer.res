open SkipruntimeCore

/** Platform to use for running the service. */
type platform = [#wasm | #native]

/** Options for running a Skip service. */
type runOptions = {
  streaming_port: int,
  control_port: int,
  platform: option<platform>,
  no_cors: option<bool>,
}

/** Running Skip service server handle. */
type skipServer

/** Run a Skip service as an HTTP server with control and streaming endpoints. */
@module("@skipruntime/server") external runService: (skipService, runOptions) => promise<skipServer> = "runService"

/** Close the server and shut down the service. */
@send external close: skipServer => promise<unit> = "close"

/** High-level ReScript-friendly API wrappers. */
module Natural = {
  let defaultOptions = {
    streaming_port: 18081,
    control_port: 18080,
    platform: Some(#wasm),
    no_cors: None,
  }

  let platformToJs = p =>
    switch p {
    | #wasm => "wasm"
    | #native => "native"
    }

  let runService = (service: skipService, ~options: option<runOptions>=?) =>
    runService(
      service,
      switch options {
      | Some(o) => o
      | None => defaultOptions
      },
    )

  let close = close
}
