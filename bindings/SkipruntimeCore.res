type depSafe = JSON.t
type watermark = string
type entry<'k, 'v> = ('k, array<'v>)
type collectionUpdate<'k, 'v> = {
  values: array<entry<'k, 'v>>,
  watermark: watermark,
  isInitial: option<bool>,
}

type eager<'k, 'v>
type lazyCollection<'k, 'v>
type context
type serviceDefinition
type serviceInstance
type serviceInstanceFactory
type subscriptionId = string
type skipService
type jsObject = JSON.t
type params = array<depSafe>
type externalResource = {
  service: string,
  identifier: string,
  params: option<JSON.t>,
}
type values<'v>
type mapperClass<'k, 'v, 'k2, 'v2>
type reducerClass<'v, 'a>
type lazyComputeClass<'k, 'v>
type notifier<'k, 'v>
type changeManager

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

type notifierSpec<'k, 'v> = {
  subscribed: unit => unit,
  notify: collectionUpdate<'k, 'v> => unit,
  close: unit => unit,
}
type changeManagerSpec = {
  needInputReload: string => bool,
  needResourceReload: string => LoadStatus.t,
  needExternalServiceReload: (string, string) => bool,
  needMapperReload: string => bool,
  needReducerReload: string => bool,
  needLazyComputeReload: string => bool,
}

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

  let skipError = msg => skipError_(msg)
  let unknownCollection = msg => unknownCollection_(msg)
  let unknownResource = msg => unknownResource_(msg)
  let rest = msg => rest_(msg)
  let fetch = msg => fetch_(msg)
  let className = msg => className_(msg)
  let nonUniqueValue = msg => nonUniqueValue_(msg)
  let resourceInUse = msg => resourceInUse_(msg)
}

module Values = {
  @send external getUnique: (values<'v>, ~ifNone: 'v=?, ~ifMany: 'v=?) => 'v = "getUnique"
  @send external toArray: values<'v> => array<'v> = "toArray"
}

module LazyCollection = {
  type t<'k, 'v> = lazyCollection<'k, 'v>

  @send external getArray: (t<'k, 'v>, 'k) => array<'v> = "getArray"
  @send
  external getUnique: (t<'k, 'v>, 'k, ~ifNone: 'v=?, ~ifMany: 'v=?) => 'v =
    "getUnique"
}

module EagerCollection = {
  type t<'k, 'v> = eager<'k, 'v>

  @send external getArray: (t<'k, 'v>, 'k) => array<'v> = "getArray"
  @send
  external getUnique: (t<'k, 'v>, 'k, ~ifNone: 'v=?, ~ifMany: 'v=?) => 'v =
    "getUnique"

  @send @variadic
  external map: (
    t<'k, 'v>,
    mapperClass<'k, 'v, 'k2, 'v2>,
    array<depSafe>
  ) => t<'k2, 'v2> = "map"

  @send @variadic
  external reduce: (
    t<'k, 'v>,
    reducerClass<'v, 'a>,
    array<depSafe>
  ) => t<'k, 'a> = "reduce"

  @send @variadic
  external mapReduce: (
    t<'k, 'v>,
    mapperClass<'k, 'v, 'k2, 'v2>,
    array<depSafe>,
    reducerClass<'v2, 'a>,
    array<depSafe>
  ) => t<'k2, 'a> = "mapReduce"

  @send external slice: (t<'k, 'v>, 'k, 'k) => t<'k, 'v> = "slice"

  @send external slices: (t<'k, 'v>, array<('k, 'k)>) => t<'k, 'v> = "slices"

  @send external take: (t<'k, 'v>, int) => t<'k, 'v> = "take"

  @send external merge: (t<'k, 'v>, array<t<'k, 'v>>) => t<'k, 'v> = "merge"

  @send external size: t<'k, 'v> => int = "size"
}

module Mapper = {
  type t<'k, 'v, 'k2, 'v2> = mapperClass<'k, 'v, 'k2, 'v2>

  @module("./SkipruntimeCoreHelpers.mjs")
  external make: (
    string,
    ('k, values<'v>, context, params) => array<('k2, 'v2)>
  ) => t<'k, 'v, 'k2, 'v2> = "makeMapperClass"
}

module Reducer = {
  type t<'v, 'a> = reducerClass<'v, 'a>

  @module("./SkipruntimeCoreHelpers.mjs")
  external make: (
    string,
    params => option<'a>,
    ('a, 'v, params) => 'a,
    ('a, 'v, params) => option<'a>
  ) => t<'v, 'a> = "makeReducerClass"
}

module LazyCompute = {
  type t<'k, 'v> = lazyComputeClass<'k, 'v>

  @module("./SkipruntimeCoreHelpers.mjs")
  external make: (
    string,
    (lazyCollection<'k, 'v>, 'k, context, params) => array<'v>
  ) => t<'k, 'v> = "makeLazyComputeClass"
}

module Notifier = {
  type t<'k, 'v> = notifier<'k, 'v>

  @module("./SkipruntimeCoreHelpers.mjs")
  external make: notifierSpec<'k, 'v> => t<'k, 'v> = "makeNotifier"
}

module ChangeManager = {
  type t = changeManager

  @module("./SkipruntimeCoreHelpers.mjs")
  external make: changeManagerSpec => t = "makeChangeManager"
}

module Context = {
  type t = context

  @send @variadic
  external createLazyCollection: (
    t,
    lazyComputeClass<'k, 'v>,
    array<depSafe>
  ) => lazyCollection<'k, 'v> = "createLazyCollection"

  @send
  external useExternalResource: (t, externalResource) => eager<'k, 'v> =
    "useExternalResource"

  @send external jsonExtract: (t, JSON.t, string) => array<JSON.t> = "jsonExtract"
}

module ServiceDefinition = {
  type t = serviceDefinition

  @module("@skipruntime/core")
  @new external make: skipService => t = "ServiceDefinition"

  @send external buildResource: (t, string, JSON.t) => jsObject = "buildResource"
  @send external inputs: t => array<string> = "inputs"
  @send external resources: t => array<string> = "resources"
  @send external initialData: (t, string) => array<entry<JSON.t, JSON.t>> =
    "initialData"

  @send
  external createGraph: (t, dict<eager<JSON.t, JSON.t>>, context) => dict<
    eager<JSON.t, JSON.t>
  > = "createGraph"

  @send
  external subscribe: (
    t,
    string,
    jsObject,
    string,
    string,
    JSON.t
  ) => promise<unit> = "subscribe"

  @send external unsubscribe: (t, string, string) => unit = "unsubscribe"
  @send external shutdown: t => promise<unit> = "shutdown"
  @send external derive: (t, skipService) => t = "derive"
}

module ServiceInstanceFactory = {
  type t = serviceInstanceFactory

  @module("@skipruntime/core")
  @new external make: (skipService => serviceInstance) => t = "ServiceInstanceFactory"

  @send external initService: (t, skipService) => serviceInstance = "initService"
}

module ServiceInstance = {
  type t = serviceInstance

  @send
  external instantiateResource: (t, string, string, JSON.t) => promise<unit> =
    "instantiateResource"

  @send
  external getAll: (t, string, option<JSON.t>) => promise<array<entry<JSON.t, JSON.t>>> =
    "getAll"

  @send
  external getArray: (t, string, JSON.t, option<JSON.t>) => promise<array<JSON.t>> =
    "getArray"

  @send external closeResourceInstance: (t, string) => unit = "closeResourceInstance"

  @send
  external subscribe: (
    t,
    string,
    notifier<'k, 'v>,
    option<watermark>
  ) => subscriptionId = "subscribe"

  @send external unsubscribe: (t, subscriptionId) => unit = "unsubscribe"

  @send
  external update: (t, string, array<entry<JSON.t, JSON.t>>) => promise<unit> =
    "update"

  @send external close: t => promise<unit> = "close"
  @send external reload: (t, skipService, changeManager) => promise<unit> =
    "reload"
}

// High-level ReScript-friendly API wrappers.
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

  module Context = {
    let createLazyCollection = (~params=?, ctx, compute) =>
      LLContext.createLazyCollection(ctx, compute, paramsOrEmpty(params))

    let useExternalResource = LLContext.useExternalResource
    let jsonExtract = LLContext.jsonExtract
  }
}
