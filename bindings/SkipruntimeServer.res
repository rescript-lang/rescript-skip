/**
 * Server bindings for running Skip reactive services.
 * 
 * This module provides ReScript bindings to @skipruntime/server, enabling
 * Skip services to be run as HTTP servers with control and streaming endpoints.
 */

open SkipruntimeCore

/** Platform to use for running the service. */
type platform = [#wasm | #native]

/**
 * Options for running a Skip service.
 * 
 * @field streaming_port Port for the SSE streaming interface.
 * @field control_port Port for the REST control interface.
 * @field platform Platform to use (wasm or native).
 * @field no_cors When set to true, disables CORS headers.
 */
type runOptions = {
  streaming_port: int,
  control_port: int,
  platform: option<platform>,
  no_cors: option<bool>,
}

/** Running Skip service server handle. */
type skipServer

/**
 * Run a Skip service as an HTTP server.
 * 
 * Starts the service with two HTTP endpoints:
 * - Control port: REST API for reading resources and writing to input collections.
 * - Streaming port: SSE API for subscribing to reactive updates.
 * 
 * @param service The SkipService to run.
 * @param options Server configuration options.
 * @returns A handle to the running server.
 */
@module("@skipruntime/server")
external runService: (skipService, runOptions) => promise<skipServer> = "runService"

/**
 * Close the server and shut down the service.
 * Any subsequent calls on the service will result in errors.
 */
@send external close: skipServer => promise<unit> = "close"

/**
 * High-level ReScript-friendly API wrappers.
 */
module Natural = {
  /** Default options for running a service (wasm platform, ports 18080/18081). */
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

  /**
   * Run a Skip service with optional configuration.
   * Uses default options if none provided.
   */
  let runService = (service: skipService, ~options: option<runOptions>=?) =>
    runService(service, switch options {
    | Some(o) => o
    | None => defaultOptions
    })

  let close = close
}
