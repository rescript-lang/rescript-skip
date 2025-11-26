/**
 * Core bindings for the Skip reactive runtime.
 * 
 * This module provides ReScript bindings to @skipruntime/core, enabling the construction
 * of reactive computation graphs with automatic incremental updates.
 */

/** Dependency-safe JSON value that can be tracked by the runtime. */
type depSafe = JSON.t

/** Opaque type used as a measure of abstract time in reactive subscriptions. */
type watermark = string

/** Association of a key to multiple values. */
type entry<'k, 'v> = ('k, array<'v>)

/**
 * Partial update to a collection.
 * 
 * @field values All updated keys and their new values. An empty array indicates deletion.
 * @field watermark A new watermark for the point after these updates.
 * @field isInitial A flag which is set when this update is the initial chunk of data rather than an update to the preceding state.
 */
type collectionUpdate<'k, 'v> = {
  values: array<entry<'k, 'v>>,
  watermark: watermark,
  isInitial: option<bool>,
}

/** An eager reactive collection, kept up-to-date automatically. */
type eager<'k, 'v>

/** A lazy reactive collection, computed on-demand. */
type lazyCollection<'k, 'v>

/** Skip Runtime internal state, used during graph construction. */
type context

/** Definition of a Skip reactive service. */
type serviceDefinition

/** Running instance of a Skip reactive service. */
type serviceInstance

/** Factory for creating service instances. */
type serviceInstanceFactory

/** Identifier for a reactive subscription. */
type subscriptionId = string

/** A Skip reactive service specification. */
type skipService

/** Generic JSON object type. */
type jsObject = JSON.t

/** Array of dependency-safe parameters. */
type params = array<depSafe>

/**
 * Reference to a resource provided by an external service.
 * 
 * @field service Name of the external service (key in SkipService.externalServices).
 * @field identifier Identifier of the resource managed by the external service.
 * @field params Optional parameters to supply to the resource.
 */
type externalResource = {
  service: string,
  identifier: string,
  params: option<JSON.t>,
}

/** A non-empty iterable sequence of dependency-safe values. */
type values<'v>

/** Mapper class for transforming collection entries. */
type mapperClass<'k, 'v, 'k2, 'v2>

/** Reducer class for accumulating values per key. */
type reducerClass<'v, 'a>

/** LazyCompute class for on-demand computation. */
type lazyComputeClass<'k, 'v>

/** Notifier for receiving reactive updates. */
type notifier<'k, 'v>

/** Manager for controlling reload behavior during hot updates. */
type changeManager

/**
 * Status of a resource after a reload check.
 * 
 * - #incompatible: Resource cannot be reused
 * - #changed: Resource changed and needs update
 * - #same: Resource unchanged, can be reused as-is
 */
module LoadStatus = {
  type t = [#incompatible | #changed | #same]

  @module("./SkipruntimeCoreHelpers.mjs")
  external loadStatusFromJsRaw: int => string = "loadStatusFromJs"

  @module("./SkipruntimeCoreHelpers.mjs")
  external loadStatusToJsRaw: string => int = "loadStatusToJs"

  let fromJs = (jsValue: int): t =>
    switch loadStatusFromJsRaw(jsValue) {
    | "incompatible" => #incompatible
    | "changed" => #changed
    | "same" => #same
    | _ => #incompatible
    }

  let toJs = (status: t): int =>
    switch status {
    | #incompatible => loadStatusToJsRaw("incompatible")
    | #changed => loadStatusToJsRaw("changed")
    | #same => loadStatusToJsRaw("same")
    }
}

/**
 * Specification for a notifier that receives reactive updates.
 * 
 * @field subscribed Called when subscription is established.
 * @field notify Called on each collection update.
 * @field close Called when the resource is closed.
 */
type notifierSpec<'k, 'v> = {
  subscribed: unit => unit,
  notify: collectionUpdate<'k, 'v> => unit,
  close: unit => unit,
}

/**
 * Specification for controlling reload behavior during hot updates.
 */
type changeManagerSpec = {
  needInputReload: string => bool,
  needResourceReload: string => LoadStatus.t,
  needExternalServiceReload: (string, string) => bool,
  needMapperReload: string => bool,
  needReducerReload: string => bool,
  needLazyComputeReload: string => bool,
}

/** Skip Runtime error types. */
module Errors = {
  @module("@skipruntime/core")
  @new external skipError_: string => JsExn.t = "SkipError"

  @module("@skipruntime/core")
  @new external unknownCollection_: string => JsExn.t = "SkipUnknownCollectionError"

  @module("@skipruntime/core")
  @new external unknownResource_: string => JsExn.t = "SkipUnknownResourceError"

  @module("@skipruntime/core")
  @new external rest_: string => JsExn.t = "SkipRESTError"

  @module("@skipruntime/core")
  @new external fetch_: string => JsExn.t = "SkipFetchError"

  @module("@skipruntime/core")
  @new external className_: string => JsExn.t = "SkipClassNameError"

  @module("@skipruntime/core")
  @new external nonUniqueValue_: string => JsExn.t = "SkipNonUniqueValueError"

  @module("@skipruntime/core")
  @new external resourceInUse_: string => JsExn.t = "SkipResourceInstanceInUseError"

  /** Create a general Skip error. */
  let skipError = msg => skipError_(msg)
  
  /** Create an error for accessing an unknown collection. */
  let unknownCollection = msg => unknownCollection_(msg)
  
  /** Create an error for accessing an unknown resource. */
  let unknownResource = msg => unknownResource_(msg)
  
  /** Create a REST API error. */
  let rest = msg => rest_(msg)
  
  /** Create a fetch error. */
  let fetch = msg => fetch_(msg)
  
  /** Create a class name error. */
  let className = msg => className_(msg)
  
  /** Create an error for non-unique value access. */
  let nonUniqueValue = msg => nonUniqueValue_(msg)
  
  /** Create an error for resource instance in use. */
  let resourceInUse = msg => resourceInUse_(msg)
}

/**
 * Operations on a non-empty sequence of values.
 * Used within mappers to access values associated with a key.
 */
module Values = {
  /**
   * Return the first value if there is exactly one.
   * @param ifMany Default value to use instead of throwing if there are multiple values.
   * @throws SkipNonUniqueValueError if this iterable contains multiple values and no default is provided.
   */
  @send external getUnique: (values<'v>, ~ifMany: 'v=?) => 'v = "getUnique"
  
  /** Return all the values as an array. */
  @send external toArray: values<'v> => array<'v> = "toArray"
}

/**
 * A lazy reactive collection whose values are computed only when queried.
 * Once an entry has been computed, later queries will not need to recompute it
 * unless its dependencies have changed.
 */
module LazyCollection = {
  type t<'k, 'v> = lazyCollection<'k, 'v>

  /** Get (and potentially compute) all values associated to a key. */
  @send external getArray: (t<'k, 'v>, 'k) => array<'v> = "getArray"
  
  /**
   * Get (and potentially compute) the single value associated to a key.
   * @param ifNone Default value for the case where zero values are associated.
   * @param ifMany Default value for the case where multiple values are associated.
   * @throws SkipNonUniqueValueError if key is associated to zero or multiple values and no suitable default is provided.
   */
  @send
  external getUnique: (t<'k, 'v>, 'k, ~ifNone: 'v=?, ~ifMany: 'v=?) => 'v =
    "getUnique"
}

/**
 * A reactive collection eagerly kept up-to-date.
 * Entries are computed eagerly and kept up to date whenever inputs change.
 */
module EagerCollection = {
  type t<'k, 'v> = eager<'k, 'v>

  /** Get all values associated to a key. */
  @send external getArray: (t<'k, 'v>, 'k) => array<'v> = "getArray"
  
  /**
   * Get the single value associated to a key.
   * @param ifNone Default value for the case where zero values are associated.
   * @param ifMany Default value for the case where multiple values are associated.
   * @throws SkipNonUniqueValueError if key is associated to zero or multiple values and no suitable default is provided.
   */
  @send
  external getUnique: (t<'k, 'v>, 'k, ~ifNone: 'v=?, ~ifMany: 'v=?) => 'v =
    "getUnique"

  /**
   * Create a new eager collection by mapping a function over the values in this one.
   * 
   * For each entry [key, values] in the collection, the mapper's mapEntry function is called
   * to produce key-value pairs. These pairs are combined to form the output collection.
   * If there are multiple pairs with the same key, the values are collected.
   * 
   * This records a dependency edge in the computation graph, so future updates to the input
   * will trigger recomputation of affected parts of the output.
   */
  @send @variadic
  external map: (
    t<'k, 'v>,
    mapperClass<'k, 'v, 'k2, 'v2>,
    array<depSafe>
  ) => t<'k2, 'v2> = "map"

  /**
   * Create a new eager collection that accumulates each key's values.
   * 
   * For each key, the reducer's add function is called on each value, starting from initial.
   * When values are removed, the reducer's remove function updates the accumulated value.
   * 
   * This records a dependency edge in the computation graph for reactive updates.
   */
  @send @variadic
  external reduce: (
    t<'k, 'v>,
    reducerClass<'v, 'a>,
    array<depSafe>
  ) => t<'k, 'a> = "reduce"

  /**
   * Composition of map and reduce.
   * More efficient than separate map().reduce() as it avoids intermediate collection.
   */
  @send @variadic
  external mapReduce: (
    t<'k, 'v>,
    mapperClass<'k, 'v, 'k2, 'v2>,
    array<depSafe>,
    reducerClass<'v2, 'a>,
    array<depSafe>
  ) => t<'k2, 'a> = "mapReduce"

  /** Create a new collection keeping only elements whose keys are in the given range. */
  @send external slice: (t<'k, 'v>, 'k, 'k) => t<'k, 'v> = "slice"

  /** Create a new collection keeping only elements whose keys are in at least one of the given ranges. */
  @send external slices: (t<'k, 'v>, array<('k, 'k)>) => t<'k, 'v> = "slices"

  /** Create a new collection keeping the first n entries. */
  @send external take: (t<'k, 'v>, int) => t<'k, 'v> = "take"

  /** Combine collections, associating with each key all values from any of the inputs. */
  @send external merge: (t<'k, 'v>, array<t<'k, 'v>>) => t<'k, 'v> = "merge"

  /** The current number of entries in the collection. */
  @send external size: t<'k, 'v> => int = "size"
}

/**
 * Factory for creating Mapper classes.
 * 
 * Mappers are reactive functions that transform collection entries.
 * Each mapper's mapEntry function produces key-value pairs from input entries.
 */
module Mapper = {
  type t<'k, 'v, 'k2, 'v2> = mapperClass<'k, 'v, 'k2, 'v2>

  /**
   * Create a mapper class from a mapping function.
   * 
   * @param name Name for the mapper class (used for identity checks during reload).
   * @param mapEntry Function that takes (key, values, context, params) and returns output key-value pairs.
   */
  @module("./SkipruntimeCoreHelpers.mjs")
  external make: (
    string,
    ('k, values<'v>, context, params) => array<('k2, 'v2)>
  ) => t<'k, 'v, 'k2, 'v2> = "makeMapperClass"
}

/**
 * Factory for creating Reducer classes.
 * 
 * Reducers are reactive functions that accumulate each key's values.
 * They maintain accumulated values efficiently as associations are added and removed.
 */
module Reducer = {
  type t<'v, 'a> = reducerClass<'v, 'a>

  /**
   * Create a reducer class from initial/add/remove functions.
   * 
   * @param name Name for the reducer class (used for identity checks during reload).
   * @param initial Function returning the initial accumulated value (None means no initial value).
   * @param add Function to include a new value into the accumulated value.
   * @param remove Function to exclude a previously added value (return None to trigger recomputation).
   */
  @module("./SkipruntimeCoreHelpers.mjs")
  external make: (
    string,
    params => option<'a>,
    ('a, 'v, params) => 'a,
    ('a, 'v, params) => option<'a>
  ) => t<'v, 'a> = "makeReducerClass"
}

/**
 * Factory for creating LazyCompute classes.
 * 
 * LazyCompute is a reactive function that is computed lazily and memoized.
 * The compute function produces values for a key, possibly using a self reference
 * to get/produce other lazily-computed results.
 */
module LazyCompute = {
  type t<'k, 'v> = lazyComputeClass<'k, 'v>

  /**
   * Create a lazy compute class from a compute function.
   * 
   * @param name Name for the lazy compute class (used for identity checks during reload).
   * @param compute Function that takes (self, key, context, params) and returns computed values.
   */
  @module("./SkipruntimeCoreHelpers.mjs")
  external make: (
    string,
    (lazyCollection<'k, 'v>, 'k, context, params) => array<'v>
  ) => t<'k, 'v> = "makeLazyComputeClass"
}

/**
 * Notifier for receiving reactive updates from a subscription.
 */
module Notifier = {
  type t<'k, 'v> = notifier<'k, 'v>

  /** Create a notifier from a specification. */
  @module("./SkipruntimeCoreHelpers.mjs")
  external make: notifierSpec<'k, 'v> => t<'k, 'v> = "makeNotifier"

  /** Manually trigger a notification with an update. */
  @send external notify: (t<'k, 'v>, collectionUpdate<'k, 'v>) => unit = "notify"
  
  /** Close the notifier. */
  @send external close: t<'k, 'v> => unit = "close"
}

/**
 * Factory for creating ChangeManager instances for hot reload control.
 */
module ChangeManager = {
  type t = changeManager

  /** Create a change manager from a specification. */
  @module("./SkipruntimeCoreHelpers.mjs")
  external make: changeManagerSpec => t = "makeChangeManager"
}

/**
 * Skip Runtime internal state.
 * Used during graph construction to create collections and access external resources.
 */
module Context = {
  type t = context

  /**
   * Create a lazy reactive collection.
   * 
   * @param compute LazyCompute class to compute entries on-demand.
   * @param params Additional parameters passed to the compute function.
   */
  @send @variadic
  external createLazyCollection: (
    t,
    lazyComputeClass<'k, 'v>,
    array<depSafe>
  ) => lazyCollection<'k, 'v> = "createLazyCollection"

  /**
   * Create an eager reactive collection populated from a resource managed by an external service.
   * 
   * The external service must be registered in the SkipService's externalServices field.
   */
  @send
  external useExternalResource: (t, externalResource) => eager<'k, 'v> =
    "useExternalResource"

  /** Extract values from a JSON object using a JSONPath-like pattern. */
  @send external jsonExtract: (t, JSON.t, string) => array<JSON.t> = "jsonExtract"

  /** Read the first event from an SSE stream (useful for initial data fetch). */
  @module("./SkipruntimeCoreHelpers.mjs")
  external readFirstSSE: string => promise<string> = "readFirstSSE"
}

/** Handle for an SSE subscription with a close method. */
type sseSubscription = {close: unit => unit}

/**
 * Subscribe to a Server-Sent Events stream.
 * 
 * @param url URL of the SSE stream to subscribe to.
 * @param onUpdate Callback invoked with each parsed JSON event.
 * @returns Subscription handle with close() method.
 */
@module("./SkipruntimeCoreHelpers.mjs")
external subscribeSSE: (string, JSON.t => unit) => sseSubscription = "subscribeSSE"

/**
 * Definition of a Skip reactive service.
 * Wraps a SkipService specification for use with the runtime.
 */
module ServiceDefinition = {
  type t = serviceDefinition

  /** Create a service definition from a SkipService. */
  @module("@skipruntime/core")
  @new external make: skipService => t = "ServiceDefinition"

  /** Build a resource with the given name and parameters. */
  @send external buildResource: (t, string, JSON.t) => jsObject = "buildResource"
  
  /** Get the names of all input collections. */
  @send external inputs: t => array<string> = "inputs"
  
  /** Get the names of all resources. */
  @send external resources: t => array<string> = "resources"
  
  /** Get the initial data for a named input collection. */
  @send external initialData: (t, string) => array<entry<JSON.t, JSON.t>> =
    "initialData"

  /** Create the reactive computation graph from input collections. */
  @send
  external createGraph: (t, dict<eager<JSON.t, JSON.t>>, context) => dict<
    eager<JSON.t, JSON.t>
  > = "createGraph"

  /** Subscribe to an external service resource. */
  @send
  external subscribe: (
    t,
    string,
    jsObject,
    string,
    string,
    JSON.t
  ) => promise<unit> = "subscribe"

  /** Unsubscribe from an external service. */
  @send external unsubscribe: (t, string, string) => unit = "unsubscribe"
  
  /** Shutdown the service and all external service connections. */
  @send external shutdown: t => promise<unit> = "shutdown"
  
  /** Derive a new service definition from an existing one. */
  @send external derive: (t, skipService) => t = "derive"
}

/**
 * Factory for creating ServiceInstance objects.
 */
module ServiceInstanceFactory = {
  type t = serviceInstanceFactory

  /** Create a factory with a custom initialization function. */
  @module("@skipruntime/core")
  @new external make: (skipService => serviceInstance) => t = "ServiceInstanceFactory"

  /** Initialize a service using the factory. */
  @send external initService: (t, skipService) => serviceInstance = "initService"
}

/**
 * A running instance of a SkipService.
 * Provides access to resources and operations to manage subscriptions and the service itself.
 */
module ServiceInstance = {
  type t = serviceInstance

  /**
   * Instantiate a resource with parameters.
   * 
   * @param identifier Resource instance identifier.
   * @param resource Resource name (must be a key in SkipService's resources field).
   * @param params Resource parameters.
   */
  @send
  external instantiateResource: (t, string, string, JSON.t) => promise<unit> =
    "instantiateResource"

  /**
   * Get all current values of a specified resource.
   * Creates the resource instance if it doesn't exist.
   */
  @send
  external getAll: (t, string, option<JSON.t>) => promise<array<entry<JSON.t, JSON.t>>> =
    "getAll"

  /**
   * Get the current values for a key in a specified resource instance.
   * Creates the resource instance if it doesn't exist.
   */
  @send
  external getArray: (t, string, JSON.t, option<JSON.t>) => promise<array<JSON.t>> =
    "getArray"

  /** Close the specified resource instance. */
  @send external closeResourceInstance: (t, string) => unit = "closeResourceInstance"

  /**
   * Initiate reactive subscription on a resource instance.
   * 
   * @param resourceInstanceId Resource instance identifier.
   * @param notifier Object containing subscription callbacks (subscribed, notify, close).
   * @param watermark Optional watermark to resume subscription from.
   * @returns Subscription identifier.
   */
  @send
  external subscribe: (
    t,
    string,
    notifier<'k, 'v>,
    option<watermark>
  ) => subscriptionId = "subscribe"

  /** Terminate a subscription. */
  @send external unsubscribe: (t, subscriptionId) => unit = "unsubscribe"

  /**
   * Update an input collection.
   * 
   * @param collection Name of the input collection to update.
   * @param entries Entries to update in the collection. Empty value array deletes the key.
   */
  @send
  external update: (t, string, array<entry<JSON.t, JSON.t>>) => promise<unit> =
    "update"

  /** Close all resources and shut down the service. */
  @send external close: t => promise<unit> = "close"
  
  /** Reload the service with new code, using the change manager to control what gets reloaded. */
  @send external reload: (t, skipService, changeManager) => promise<unit> =
    "reload"
}

/**
 * High-level ReScript-friendly API wrappers.
 * 
 * The Natural module provides more idiomatic ReScript interfaces that wrap
 * the low-level bindings with better ergonomics (optional params, labeled arguments).
 */
module Natural = {
  module LLEagerCollection = EagerCollection
  module LLMapper = Mapper
  module LLReducer = Reducer
  module LLLazyCompute = LazyCompute
  module LLContext = Context

  let emptyParams: array<depSafe> = []

  let paramsOrEmpty = (p: option<array<depSafe>>): array<depSafe> =>
    switch p {
    | Some(v) => v
    | None => emptyParams
    }

  /** Mapper with simplified creation (no name required). */
  module Mapper = {
    let make = mapEntry => LLMapper.make("Mapper", mapEntry)
  }

  /** Reducer with simplified creation (no name required, optional remove). */
  module Reducer = {
    let make = (~initial, ~add, ~remove=?) =>
      LLReducer.make(
        "Reducer",
        initial,
        add,
        switch remove {
        | Some(r) => r
        | None => (_acc, _value, _params) => None
        },
      )
  }

  /** LazyCompute with simplified creation (no name required). */
  module LazyCompute = {
    let make = compute => LLLazyCompute.make("LazyCompute", compute)
  }

  /** EagerCollection with optional params for map/reduce operations. */
  module EagerCollection = {
    let getArray = LLEagerCollection.getArray
    let getUnique = LLEagerCollection.getUnique
    let size = LLEagerCollection.size

    let map = (~params=?, collection, mapper) =>
      LLEagerCollection.map(collection, mapper, paramsOrEmpty(params))

    let reduce = (~params=?, collection, reducer) =>
      LLEagerCollection.reduce(collection, reducer, paramsOrEmpty(params))

    let mapReduce = (
      ~mapperParams=?,
      ~reducerParams=?,
      collection,
      mapper,
      reducer,
    ) =>
      LLEagerCollection.mapReduce(
        collection,
        mapper,
        paramsOrEmpty(mapperParams),
        reducer,
        paramsOrEmpty(reducerParams),
      )

    let slice = LLEagerCollection.slice
    let slices = LLEagerCollection.slices
    let take = LLEagerCollection.take
    let merge = LLEagerCollection.merge
  }

  /** Context with optional params for lazy collection creation. */
  module Context = {
    let createLazyCollection = (~params=?, ctx, compute) =>
      LLContext.createLazyCollection(ctx, compute, paramsOrEmpty(params))

    let useExternalResource = LLContext.useExternalResource
    let jsonExtract = LLContext.jsonExtract
  }
}
