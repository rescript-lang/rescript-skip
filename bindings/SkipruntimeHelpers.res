open SkipruntimeCore

type entrypoint = {
  host: string,
  streaming_port: int,
  control_port: int,
  secured: option<bool>,
}

type broker

@module("@skipruntime/helpers")
@new external make: (entrypoint, option<int>) => broker = "SkipServiceBroker"

@send external getAll: (broker, string, JSON.t) => promise<array<entry<JSON.t, JSON.t>>> =
  "getAll"

@send external update: (broker, string, array<entry<JSON.t, JSON.t>>) => promise<unit> =
  "update"

@send external getStreamUUID: (broker, string, JSON.t) => promise<string> =
  "getStreamUUID"

// Built-in reducers: native implementations for common aggregations.
// Use with EagerCollection.reduce(collection, reducer).

module Sum = {
  type t
  @module("@skipruntime/helpers") @new external make: unit => t = "Sum"
}

module Min = {
  type t
  @module("@skipruntime/helpers") @new external make: unit => t = "Min"
}

module Max = {
  type t
  @module("@skipruntime/helpers") @new external make: unit => t = "Max"
}

module Count = {
  type t
  @module("@skipruntime/helpers") @new external make: unit => t = "Count"
}
