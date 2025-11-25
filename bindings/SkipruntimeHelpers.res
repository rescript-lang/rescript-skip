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

@send external getAll: (broker, string, json) => promise<array<entry<json, json>>> =
  "getAll"

@send external update: (broker, string, array<entry<json, json>>) => promise<unit> =
  "update"

@send external getStreamUUID: (broker, string, json) => promise<string> =
  "getStreamUUID"
