// Service for harness: one input, derived resources using mapper/reducer.
import {
  type EagerCollection,
  type Mapper,
  type Reducer,
  type Resource,
  type Values,
  type SkipService,
  type Json,
} from "@skipruntime/core";

// Mapper: multiply numeric values by 2, keep the same key.
class DoubleMapper implements Mapper<string, Json, string, Json> {
  mapEntry(key: string, values: Values<Json>): Iterable<[string, Json]> {
    const n = values.getUnique();
    return [[key, typeof n === "number" ? n * 2 : n]] as [string, Json][];
  }
}

// Mapper: emit all values under a single "total" key for reduction.
class TotalMapper implements Mapper<string, Json, string, Json> {
  mapEntry(_key: string, values: Values<Json>): Iterable<[string, Json]> {
    return values.toArray().map((v) => ["total", v]) as [string, Json][];
  }
}

// Reducer: sum numbers with seed 0.
class SumReducer implements Reducer<Json, Json> {
  initial: Json = 0;
  add(acc: Json, value: Json): Json {
    const a = typeof acc === "number" ? acc : 0;
    const n = typeof value === "number" ? value : 0;
    return a + n;
  }
  remove(acc: Json, _value: Json): Json {
    return acc;
  }
}

class NumbersResource implements Resource<{ numbers: EagerCollection<string, Json> }> {
  instantiate(collections: { numbers: EagerCollection<string, Json> }): EagerCollection<string, Json> {
    return collections.numbers;
  }
}

class DoubledResource implements Resource<{ numbers: EagerCollection<string, Json> }> {
  instantiate(collections: { numbers: EagerCollection<string, Json> }): EagerCollection<string, Json> {
    return collections.numbers.map(DoubleMapper);
  }
}

class SumResource implements Resource<{ numbers: EagerCollection<string, Json> }> {
  instantiate(collections: { numbers: EagerCollection<string, Json> }): EagerCollection<string, Json> {
    return collections.numbers.map(TotalMapper).reduce(SumReducer);
  }
}

export const service: SkipService = {
  initialData: {
    numbers: [
      ["a", [1]],
      ["b", [2]],
    ],
  },
  resources: {
    numbers: NumbersResource,
    doubled: DoubledResource,
    sum: SumResource,
  },
  createGraph: (inputs) => inputs,
};
