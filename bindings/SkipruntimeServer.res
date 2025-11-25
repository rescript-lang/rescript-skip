open SkipruntimeCore

type platform = [#wasm | #native]

type runOptions = {
  streaming_port: int,
  control_port: int,
  platform: option<platform>,
  no_cors: option<bool>,
}

type skipServer

@module("@skipruntime/server")
external runService: (skipService, runOptions) => promise<skipServer> = "runService"

@send external close: skipServer => promise<unit> = "close"

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
    runService(service, switch options {
    | Some(o) => o
    | None => defaultOptions
    })

  let close = close
}
