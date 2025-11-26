open SkipruntimeCore

/** An entry point of a Skip reactive service with host and ports. */
type entrypoint = {
  host: string,
  streaming_port: int,
  control_port: int,
  secured: option<bool>,
}

/** Broker providing method-call interface to Skip service HTTP APIs. */
type broker

/** Construct a broker for a Skip service at the given entry point. */
@module("@skipruntime/helpers") @new external make: (option<entrypoint>, option<int>) => broker = "SkipServiceBroker"

/** Read the entire contents of a resource. */
@send external getAll: (broker, string, JSON.t) => promise<array<entry<JSON.t, JSON.t>>> = "getAll"

/** Read the values a resource associates with a single key. */
@send external getArray: (broker, string, JSON.t, JSON.t) => promise<array<JSON.t>> = "getArray"

/** Read the single value a resource associates with a key. */
@send external getUnique: (broker, string, JSON.t, JSON.t) => promise<JSON.t> = "getUnique"

/** Write multiple entries to an input collection. */
@send external update: (broker, string, array<entry<JSON.t, JSON.t>>) => promise<unit> = "update"

/** Remove all values associated with a key in a collection. */
@send external deleteKey: (broker, string, JSON.t) => promise<unit> = "deleteKey"

/** Create a resource instance UUID for SSE streaming. */
@send external getStreamUUID: (broker, string, option<JSON.t>) => promise<string> = "getStreamUUID"

/** Destroy a resource instance immediately. */
@send external deleteUUID: (broker, string) => promise<unit> = "deleteUUID"

// Built-in reducers

/** Reducer to maintain the sum of input values. */
module Sum = {
  type t
  @module("@skipruntime/helpers") @new external make: unit => t = "Sum"
}

/** Reducer to maintain the minimum of input values. */
module Min = {
  type t
  @module("@skipruntime/helpers") @new external make: unit => t = "Min"
}

/** Reducer to maintain the maximum of input values. */
module Max = {
  type t
  @module("@skipruntime/helpers") @new external make: unit => t = "Max"
}

/** Reducer to maintain the count of input values. */
module Count = {
  type t
  @module("@skipruntime/helpers") @new external make: unit => t = "Count"
}

// External service helpers

/** Callbacks for external service subscriptions. */
type externalCallbacks = {
  update: (array<entry<JSON.t, JSON.t>>, bool) => promise<unit>,
  error: JsExn.t => unit,
}

/** Configuration for a polled HTTP resource. */
type polledHTTPResource = {
  url: string,
  interval: int,
  conv: JSON.t => array<entry<JSON.t, JSON.t>>,
  options: option<JSON.t>,
  encodeParams: option<JSON.t => string>,
}

/** External service interface. */
type externalService

/** An external HTTP service kept up-to-date by polling. */
module PolledExternalService = {
  type t = externalService

  /** Construct a polled external service from resource specifications. */
  @module("@skipruntime/helpers") @new external make: Dict.t<polledHTTPResource> => t = "PolledExternalService"

  /** Subscribe to a resource provided by the external service. */
  @send external subscribe: (t, string, string, JSON.t, externalCallbacks) => promise<unit> = "subscribe"

  /** Unsubscribe from a resource. */
  @send external unsubscribe: (t, string) => unit = "unsubscribe"

  /** Shutdown the external service. */
  @send external shutdown: t => promise<unit> = "shutdown"
}

/** An external Skip reactive service. */
module SkipExternalService = {
  type t = externalService

  /** Construct from streaming and control URLs. */
  @module("@skipruntime/helpers") @new external make: (string, string) => t = "SkipExternalService"

  /** Construct from an Entrypoint. */
  @module("@skipruntime/helpers") @scope("SkipExternalService") external direct: entrypoint => t = "direct"

  /** Subscribe to a resource provided by the external service. */
  @send external subscribe: (t, string, string, JSON.t, externalCallbacks) => promise<unit> = "subscribe"

  /** Unsubscribe from a resource. */
  @send external unsubscribe: (t, string) => unit = "unsubscribe"

  /** Shutdown the external service. */
  @send external shutdown: t => promise<unit> = "shutdown"
}

/** Configuration for a follower in leader-follower topology. */
type leaderConfig = {
  leader: entrypoint,
  collections: array<string>,
}

/** Run a SkipService as the leader in a leader-follower topology. */
@module("@skipruntime/helpers") external asLeader: skipService => skipService = "asLeader"

/** Run a SkipService as a follower in a leader-follower topology. */
@module("@skipruntime/helpers") external asFollower: (skipService, leaderConfig) => skipService = "asFollower"
