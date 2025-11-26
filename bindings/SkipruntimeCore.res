/** Dependency-safe JSON value that can be tracked by the runtime. */
type depSafe = JSON.t

/** Opaque type used as a measure of abstract time in reactive subscriptions. */
type watermark = string

/** Association of a key to multiple values. */
type entry<'k, 'v> = ('k, array<'v>)

/** Partial update to a collection with values, watermark, and isInitial flag. */
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

/** Reference to a resource provided by an external service. */
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

/** Status of a resource after a reload check: `#incompatible`, `#changed`, or `#same`. */
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

/** Specification for a notifier that receives reactive updates. */
type notifierSpec<'k, 'v> = {
  subscribed: unit => unit,
  notify: collectionUpdate<'k, 'v> => unit,
  close: unit => unit,
}

/** Specification for controlling reload behavior during hot updates. */
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
  @module("@skipruntime/core") @new external skipError_: string => JsExn.t = "SkipError"
  @module("@skipruntime/core") @new external unknownCollection_: string => JsExn.t = "SkipUnknownCollectionError"
  @module("@skipruntime/core") @new external unknownResource_: string => JsExn.t = "SkipUnknownResourceError"
  @module("@skipruntime/core") @new external rest_: string => JsExn.t = "SkipRESTError"
  @module("@skipruntime/core") @new external fetch_: string => JsExn.t = "SkipFetchError"
  @module("@skipruntime/core") @new external className_: string => JsExn.t = "SkipClassNameError"
  @module("@skipruntime/core") @new external nonUniqueValue_: string => JsExn.t = "SkipNonUniqueValueError"
  @module("@skipruntime/core") @new external resourceInUse_: string => JsExn.t = "SkipResourceInstanceInUseError"

  let skipError = msg => skipError_(msg)
  let unknownCollection = msg => unknownCollection_(msg)
  let unknownResource = msg => unknownResource_(msg)
  let rest = msg => rest_(msg)
  let fetch = msg => fetch_(msg)
  let className = msg => className_(msg)
  let nonUniqueValue = msg => nonUniqueValue_(msg)
  let resourceInUse = msg => resourceInUse_(msg)
}

/** Operations on a non-empty sequence of values within mappers. */
module Values = {
  /** Return the first value if there is exactly one; throws if multiple values and no `ifMany` default. */
  @send external getUnique: (values<'v>, ~ifMany: 'v=?) => 'v = "getUnique"

  /** Return all the values as an array. */
  @send external toArray: values<'v> => array<'v> = "toArray"
}

/** A lazy reactive collection whose values are computed only when queried. */
module LazyCollection = {
  type t<'k, 'v> = lazyCollection<'k, 'v>

  /** Get (and potentially compute) all values associated to a key. */
  @send external getArray: (t<'k, 'v>, 'k) => array<'v> = "getArray"

  /** Get the single value associated to a key; throws if zero/multiple values and no defaults. */
  @send external getUnique: (t<'k, 'v>, 'k, ~ifNone: 'v=?, ~ifMany: 'v=?) => 'v = "getUnique"
}

/** A reactive collection eagerly kept up-to-date. */
module EagerCollection = {
  type t<'k, 'v> = eager<'k, 'v>

  /** Get all values associated to a key. */
  @send external getArray: (t<'k, 'v>, 'k) => array<'v> = "getArray"

  /** Get the single value associated to a key; throws if zero/multiple values and no defaults. */
  @send external getUnique: (t<'k, 'v>, 'k, ~ifNone: 'v=?, ~ifMany: 'v=?) => 'v = "getUnique"

  /** Create a new collection by mapping a function over entries. */
  @send @variadic
  external map: (t<'k, 'v>, mapperClass<'k, 'v, 'k2, 'v2>, array<depSafe>) => t<'k2, 'v2> = "map"

  /** Create a new collection that accumulates each key's values. */
  @send @variadic
  external reduce: (t<'k, 'v>, reducerClass<'v, 'a>, array<depSafe>) => t<'k, 'a> = "reduce"

  /** Composition of `map` and `reduce`, more efficient than chaining. */
  @send @variadic
  external mapReduce: (
    t<'k, 'v>,
    mapperClass<'k, 'v, 'k2, 'v2>,
    array<depSafe>,
    reducerClass<'v2, 'a>,
    array<depSafe>,
  ) => t<'k2, 'a> = "mapReduce"

  /** Keep only elements whose keys are in the given range. */
  @send external slice: (t<'k, 'v>, 'k, 'k) => t<'k, 'v> = "slice"

  /** Keep only elements whose keys are in at least one of the given ranges. */
  @send external slices: (t<'k, 'v>, array<('k, 'k)>) => t<'k, 'v> = "slices"

  /** Keep the first n entries. */
  @send external take: (t<'k, 'v>, int) => t<'k, 'v> = "take"

  /** Combine collections, associating with each key all values from any input. */
  @send external merge: (t<'k, 'v>, array<t<'k, 'v>>) => t<'k, 'v> = "merge"

  /** The current number of entries in the collection. */
  @send external size: t<'k, 'v> => int = "size"
}

/** Factory for creating Mapper classes that transform collection entries. */
module Mapper = {
  type t<'k, 'v, 'k2, 'v2> = mapperClass<'k, 'v, 'k2, 'v2>

  /** Create a mapper class from a mapping function. */
  @module("./SkipruntimeCoreHelpers.mjs")
  external make: (string, ('k, values<'v>, context, params) => array<('k2, 'v2)>) => t<'k, 'v, 'k2, 'v2> = "makeMapperClass"
}

/** Factory for creating Reducer classes that accumulate values per key. */
module Reducer = {
  type t<'v, 'a> = reducerClass<'v, 'a>

  /** Create a reducer class from initial/add/remove functions. */
  @module("./SkipruntimeCoreHelpers.mjs")
  external make: (
    string,
    params => option<'a>,
    ('a, 'v, params) => 'a,
    ('a, 'v, params) => option<'a>,
  ) => t<'v, 'a> = "makeReducerClass"
}

/** Factory for creating LazyCompute classes for on-demand computation. */
module LazyCompute = {
  type t<'k, 'v> = lazyComputeClass<'k, 'v>

  /** Create a lazy compute class from a compute function. */
  @module("./SkipruntimeCoreHelpers.mjs")
  external make: (string, (lazyCollection<'k, 'v>, 'k, context, params) => array<'v>) => t<'k, 'v> = "makeLazyComputeClass"
}

/** Notifier for receiving reactive updates from a subscription. */
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

/** Factory for creating ChangeManager instances for hot reload control. */
module ChangeManager = {
  type t = changeManager

  /** Create a change manager from a specification. */
  @module("./SkipruntimeCoreHelpers.mjs")
  external make: changeManagerSpec => t = "makeChangeManager"
}

/** Skip Runtime internal state for creating collections and accessing external resources. */
module Context = {
  type t = context

  /** Create a lazy reactive collection. */
  @send @variadic
  external createLazyCollection: (t, lazyComputeClass<'k, 'v>, array<depSafe>) => lazyCollection<'k, 'v> = "createLazyCollection"

  /** Create an eager collection populated from an external service resource. */
  @send external useExternalResource: (t, externalResource) => eager<'k, 'v> = "useExternalResource"

  /** Extract values from a JSON object using a JSONPath-like pattern. */
  @send external jsonExtract: (t, JSON.t, string) => array<JSON.t> = "jsonExtract"

  /** Read the first event from an SSE stream (useful for initial data fetch). */
  @module("./SkipruntimeCoreHelpers.mjs")
  external readFirstSSE: string => promise<string> = "readFirstSSE"
}

/** Handle for an SSE subscription with a `close` method. */
type sseSubscription = {close: unit => unit}

/** Subscribe to a Server-Sent Events stream, calling `onUpdate` for each event. */
@module("./SkipruntimeCoreHelpers.mjs")
external subscribeSSE: (string, JSON.t => unit) => sseSubscription = "subscribeSSE"

/** Definition of a Skip reactive service. */
module ServiceDefinition = {
  type t = serviceDefinition

  /** Create a service definition from a SkipService. */
  @module("@skipruntime/core") @new external make: skipService => t = "ServiceDefinition"

  /** Build a resource with the given name and parameters. */
  @send external buildResource: (t, string, JSON.t) => jsObject = "buildResource"

  /** Get the names of all input collections. */
  @send external inputs: t => array<string> = "inputs"

  /** Get the names of all resources. */
  @send external resources: t => array<string> = "resources"

  /** Get the initial data for a named input collection. */
  @send external initialData: (t, string) => array<entry<JSON.t, JSON.t>> = "initialData"

  /** Create the reactive computation graph from input collections. */
  @send external createGraph: (t, dict<eager<JSON.t, JSON.t>>, context) => dict<eager<JSON.t, JSON.t>> = "createGraph"

  /** Subscribe to an external service resource. */
  @send external subscribe: (t, string, jsObject, string, string, JSON.t) => promise<unit> = "subscribe"

  /** Unsubscribe from an external service. */
  @send external unsubscribe: (t, string, string) => unit = "unsubscribe"

  /** Shutdown the service and all external service connections. */
  @send external shutdown: t => promise<unit> = "shutdown"

  /** Derive a new service definition from an existing one. */
  @send external derive: (t, skipService) => t = "derive"
}

/** Factory for creating ServiceInstance objects. */
module ServiceInstanceFactory = {
  type t = serviceInstanceFactory

  /** Create a factory with a custom initialization function. */
  @module("@skipruntime/core") @new external make: (skipService => serviceInstance) => t = "ServiceInstanceFactory"

  /** Initialize a service using the factory. */
  @send external initService: (t, skipService) => serviceInstance = "initService"
}

/** A running instance of a SkipService with access to resources and subscriptions. */
module ServiceInstance = {
  type t = serviceInstance

  /** Instantiate a resource with parameters. */
  @send external instantiateResource: (t, string, string, JSON.t) => promise<unit> = "instantiateResource"

  /** Get all current values of a specified resource. */
  @send external getAll: (t, string, option<JSON.t>) => promise<array<entry<JSON.t, JSON.t>>> = "getAll"

  /** Get the current values for a key in a specified resource instance. */
  @send external getArray: (t, string, JSON.t, option<JSON.t>) => promise<array<JSON.t>> = "getArray"

  /** Close the specified resource instance. */
  @send external closeResourceInstance: (t, string) => unit = "closeResourceInstance"

  /** Initiate reactive subscription on a resource instance. */
  @send external subscribe: (t, string, notifier<'k, 'v>, option<watermark>) => subscriptionId = "subscribe"

  /** Terminate a subscription. */
  @send external unsubscribe: (t, subscriptionId) => unit = "unsubscribe"

  /** Update an input collection. */
  @send external update: (t, string, array<entry<JSON.t, JSON.t>>) => promise<unit> = "update"

  /** Close all resources and shut down the service. */
  @send external close: t => promise<unit> = "close"

  /** Reload the service with new code using the change manager. */
  @send external reload: (t, skipService, changeManager) => promise<unit> = "reload"
}

/** High-level ReScript-friendly API wrappers with optional params and labeled arguments. */
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

  module Mapper = {
    let make = mapEntry => LLMapper.make("Mapper", mapEntry)
  }

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

  module LazyCompute = {
    let make = compute => LLLazyCompute.make("LazyCompute", compute)
  }

  module EagerCollection = {
    let getArray = LLEagerCollection.getArray
    let getUnique = LLEagerCollection.getUnique
    let size = LLEagerCollection.size

    let map = (~params=?, collection, mapper) =>
      LLEagerCollection.map(collection, mapper, paramsOrEmpty(params))

    let reduce = (~params=?, collection, reducer) =>
      LLEagerCollection.reduce(collection, reducer, paramsOrEmpty(params))

    let mapReduce = (~mapperParams=?, ~reducerParams=?, collection, mapper, reducer) =>
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

  module Context = {
    let createLazyCollection = (~params=?, ctx, compute) =>
      LLContext.createLazyCollection(ctx, compute, paramsOrEmpty(params))

    let useExternalResource = LLContext.useExternalResource
    let jsonExtract = LLContext.jsonExtract
  }
}
