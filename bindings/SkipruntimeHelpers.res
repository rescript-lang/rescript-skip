/**
 * Helper utilities for working with Skip reactive services.
 * 
 * This module provides ReScript bindings to @skipruntime/helpers, including:
 * - SkipServiceBroker for method-call access to service HTTP APIs
 * - Built-in reducers (Sum, Min, Max, Count)
 * - External service helpers for distributed/federated architectures
 */

open SkipruntimeCore

/**
 * An entry point of a Skip reactive service.
 * URLs for the service's control and streaming APIs can be constructed from an Entrypoint.
 * 
 * @field host Hostname of the service.
 * @field streaming_port Port to use for the service's streaming interface.
 * @field control_port Port to use for the service's control interface.
 * @field secured When set, indicates that https should be used instead of http.
 */
type entrypoint = {
  host: string,
  streaming_port: int,
  control_port: int,
  secured: option<bool>,
}

/** Broker providing method-call interface to Skip service HTTP APIs. */
type broker

/**
 * Construct a broker for a Skip service at the given entry point.
 * 
 * @param entrypoint Entry point of backing service. Defaults to localhost:18080/18081.
 * @param timeout Timeout for requests in milliseconds. Defaults to 1000ms.
 */
@module("@skipruntime/helpers")
@new external make: (option<entrypoint>, option<int>) => broker = "SkipServiceBroker"

/**
 * Read the entire contents of a resource.
 * 
 * **resource**: Name of resource (must be a key in the SkipService's resources field).
 * **params**: Resource instance parameters.
 * **returns**: All entries in resource.
 */
@send external getAll: (broker, string, JSON.t) => promise<array<entry<JSON.t, JSON.t>>> =
  "getAll"

/**
 * Read the values a resource associates with a single key.
 * 
 * @param resource Name of resource (must be a key in the SkipService's resources field).
 * @param params Resource instance parameters.
 * @param key Key to read.
 * @returns The values associated to the key.
 */
@send external getArray: (broker, string, JSON.t, JSON.t) => promise<array<JSON.t>> =
  "getArray"

/**
 * Read the single value a resource associates with a key.
 * 
 * @param resource Name of resource (must be a key in the SkipService's resources field).
 * @param params Resource instance parameters.
 * @param key Key to read.
 * @returns The value associated to the key.
 * @throws SkipNonUniqueValueError when the key is associated to either zero or multiple values.
 */
@send external getUnique: (broker, string, JSON.t, JSON.t) => promise<JSON.t> =
  "getUnique"

/**
 * Write multiple entries to an input collection.
 * 
 * @param collection Name of the input collection to update.
 * @param entries Entries to write. Empty value array deletes the key.
 */
@send external update: (broker, string, array<entry<JSON.t, JSON.t>>) => promise<unit> =
  "update"

/**
 * Remove all values associated with a key in a collection.
 * 
 * @param collection Name of the input collection to update.
 * @param key Key of entry to delete.
 */
@send external deleteKey: (broker, string, JSON.t) => promise<unit> =
  "deleteKey"

/**
 * Create a resource instance UUID for SSE streaming.
 * 
 * @param resource Name of resource (must be a key in the SkipService's resources field).
 * @param params Resource instance parameters.
 * @returns UUID that can be used to subscribe to updates to resource instance.
 */
@send external getStreamUUID: (broker, string, option<JSON.t>) => promise<string> =
  "getStreamUUID"

/**
 * Destroy a resource instance.
 * 
 * Under normal circumstances, resource instances are deleted automatically after
 * some period of inactivity; this method enables immediately deleting live streams.
 * 
 * @param uuid Resource instance UUID.
 */
@send external deleteUUID: (broker, string) => promise<unit> =
  "deleteUUID"

// ============================================================================
// Built-in reducers: native implementations for common aggregations.
// Use with EagerCollection.reduce(collection, reducer).
// ============================================================================

/**
 * Reducer to maintain the sum of input values.
 * Maintains the sum of values as they are added and removed from a collection.
 */
module Sum = {
  type t
  @module("@skipruntime/helpers") @new external make: unit => t = "Sum"
}

/**
 * Reducer to maintain the minimum of input values.
 * Maintains the minimum of values as they are added and removed from a collection.
 * Note: remove returns null, triggering recomputation.
 */
module Min = {
  type t
  @module("@skipruntime/helpers") @new external make: unit => t = "Min"
}

/**
 * Reducer to maintain the maximum of input values.
 * Maintains the maximum of values as they are added and removed from a collection.
 * Note: remove returns null, triggering recomputation.
 */
module Max = {
  type t
  @module("@skipruntime/helpers") @new external make: unit => t = "Max"
}

/**
 * Reducer to maintain the count of input values.
 * Maintains the number of values as they are added and removed from a collection.
 */
module Count = {
  type t
  @module("@skipruntime/helpers") @new external make: unit => t = "Count"
}

// ============================================================================
// External service helpers for distributed/federated architectures.
// ============================================================================

/**
 * Callbacks for external service subscriptions.
 * 
 * @field update Callback invoked with updates (entries and isInit flag).
 * @field error Callback invoked when an error prevents an update.
 */
type externalCallbacks = {
  update: (array<entry<JSON.t, JSON.t>>, bool) => promise<unit>,
  error: JsExn.t => unit,
}

/**
 * Configuration for a polled HTTP resource.
 * 
 * @field url Base URL of resource to poll.
 * @field interval Interval in milliseconds between polls.
 * @field conv Function to convert received data to key-value entries.
 * @field encodeParams Function to encode params for the request URL.
 * @field options Additional headers and timeout configuration.
 */
type polledHTTPResource = {
  url: string,
  interval: int,
  conv: JSON.t => array<entry<JSON.t, JSON.t>>,
  options: option<JSON.t>,
  encodeParams: option<JSON.t => string>,
}

/** External service interface (implemented by PolledExternalService and SkipExternalService). */
type externalService

/**
 * An external HTTP service that is kept up-to-date by polling.
 * 
 * A PolledExternalService may be composed of one or more PolledHTTPResources,
 * each of which describes a single endpoint and how to poll it.
 */
module PolledExternalService = {
  type t = externalService

  /**
   * Construct a polled external service.
   * 
   * @param resources Specification(s) of external resource(s) to poll, keyed by resource name.
   */
  @module("@skipruntime/helpers")
  @new external make: Dict.t<polledHTTPResource> => t = "PolledExternalService"

  /**
   * Subscribe to a resource provided by the external service.
   * 
   * @param instance Instance identifier of the external resource.
   * @param resource Name of the external resource.
   * @param params Parameters of the external resource.
   * @param callbacks Callbacks to react on error/update.
   */
  @send external subscribe: (
    t,
    string,
    string,
    JSON.t,
    externalCallbacks
  ) => promise<unit> = "subscribe"

  /** Unsubscribe from a resource. */
  @send external unsubscribe: (t, string) => unit = "unsubscribe"
  
  /** Shutdown the external service. */
  @send external shutdown: t => promise<unit> = "shutdown"
}

/**
 * An external Skip reactive service.
 * 
 * SkipExternalService provides an ExternalService implementation for
 * connecting to another Skip service and subscribing to its resources.
 */
module SkipExternalService = {
  type t = externalService

  /**
   * Construct a Skip external service.
   * 
   * @param url URL for the service's streaming interface.
   * @param control_url URL for the service's control interface.
   */
  @module("@skipruntime/helpers")
  @new external make: (string, string) => t = "SkipExternalService"

  /**
   * Construct from an Entrypoint.
   * 
   * @param entrypoint The entry point for the external Skip service.
   */
  @module("@skipruntime/helpers") @scope("SkipExternalService")
  external direct: entrypoint => t = "direct"

  /**
   * Subscribe to a resource provided by the external service.
   * 
   * @param instance Instance identifier of the external resource.
   * @param resource Name of the external resource.
   * @param params Parameters of the external resource.
   * @param callbacks Callbacks to react on error/update.
   */
  @send external subscribe: (
    t,
    string,
    string,
    JSON.t,
    externalCallbacks
  ) => promise<unit> = "subscribe"

  /** Unsubscribe from a resource. */
  @send external unsubscribe: (t, string) => unit = "unsubscribe"
  
  /** Shutdown the external service. */
  @send external shutdown: t => promise<unit> = "shutdown"
}

/**
 * Configuration for a follower in leader-follower topology.
 * 
 * @field leader The leader's entrypoint (host, streaming_port, control_port).
 * @field collections Names of shared computation graph collections to mirror from leader.
 */
type leaderConfig = {
  leader: entrypoint,
  collections: array<string>,
}

/**
 * Run a SkipService as the leader in a leader-follower topology.
 * 
 * Instead of running a service on one machine, it can be distributed across multiple
 * in a leader-follower architecture, with one "leader" maintaining the shared computation
 * graph and one or more "followers" across which client-requested resource instances are distributed.
 * 
 * @param service The service to run as leader.
 * @returns The leader component to run the service.
 */
@module("@skipruntime/helpers")
external asLeader: skipService => skipService = "asLeader"

/**
 * Run a SkipService as a follower in a leader-follower topology.
 * 
 * The follower component mirrors specified collections from the leader and handles
 * client-requested resource instances locally.
 * 
 * @param service The service to run as follower.
 * @param config Leader address and collections to mirror.
 * @returns The follower component to run the service.
 */
@module("@skipruntime/helpers")
external asFollower: (skipService, leaderConfig) => skipService = "asFollower"
