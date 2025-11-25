// Helper constructors and adapters for @skipruntime/core bindings.

const setName = (klass, name) => {
  if (name && klass.name !== name) {
    Object.defineProperty(klass, "name", { value: name });
  }
  return klass;
};

export const makeMapperClass = (name, mapEntry) =>
  setName(
    class Mapper {
      constructor(...params) {
        this._params = params;
        Object.freeze(this);
      }
      mapEntry(key, values, context) {
        return mapEntry(key, values, context, this._params);
      }
    },
    name,
  );

export const makeReducerClass = (name, initial, add, remove) =>
  setName(
    class Reducer {
      constructor(...params) {
        this._params = params;
        this.initial =
          typeof initial === "function" ? initial(...params) : initial;
        Object.freeze(this);
      }
      add(accum, value) {
        return add(accum, value, this._params);
      }
      remove(accum, value) {
        return remove(accum, value, this._params);
      }
    },
    name,
  );

export const makeLazyComputeClass = (name, compute) =>
  setName(
    class LazyCompute {
      constructor(...params) {
        this._params = params;
        Object.freeze(this);
      }
      compute(self, key, context) {
        return compute(self, key, context, this._params);
      }
    },
    name,
  );

export const makeNotifier = ({ subscribed, notify, close }) => ({
  subscribed,
  notify,
  close,
});

export const makeChangeManager = (impl) => ({
  needInputReload: impl.needInputReload,
  needResourceReload: impl.needResourceReload,
  needExternalServiceReload: impl.needExternalServiceReload,
  needMapperReload: impl.needMapperReload,
  needReducerReload: impl.needReducerReload,
  needLazyComputeReload: impl.needLazyComputeReload,
});

export const loadStatusFromJs = (value) => {
  switch (value) {
    case 0:
      return "incompatible";
    case 1:
      return "changed";
    case 2:
      return "same";
    default:
      return "incompatible";
  }
};

export const loadStatusToJs = (tag) => {
  switch (tag) {
    case "incompatible":
      return 0;
    case "changed":
      return 1;
    case "same":
      return 2;
    default:
      return 0;
  }
};

// Read the first SSE chunk from a stream URL, then abort.
export async function readFirstSSE(url) {
  const controller = new AbortController();
  const res = await fetch(url, {
    signal: controller.signal,
    headers: { Accept: "text/event-stream" },
  });
  const reader = res.body.getReader();
  const decoder = new TextDecoder();
  const { value, done } = await reader.read();
  controller.abort();
  if (done || !value) return "";
  return decoder.decode(value);
}
