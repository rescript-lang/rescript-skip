// Service for harness: one input, derived resources using mapper/reducer.
import {
  type Context,
  type EagerCollection,
  type Mapper,
  type Reducer,
  type Resource,
  type Values,
  type SkipService,
} from "@skipruntime/core";

const ENABLE_LOGS = process.env["SKIP_HARNESS_LOGS"] === "1";
const log = (...args: unknown[]) => {
  if (ENABLE_LOGS) console.log(...args);
};

type Collections = {
  numbers: EagerCollection<string, number>;
};

// Mapper: multiply numeric values by 2, keep the same key.
class DoubleMapper implements Mapper<string, number, string, number> {
  static runs = 0;
  mapEntry(key: string, values: Values<number>, _ctx: Context): Iterable<[string, number]> {
    DoubleMapper.runs += 1;
    log("mapper:doubled run", DoubleMapper.runs, "key", key);
    const n = values.getUnique();
    return [[key, n * 2]];
  }
}

// Mapper for sum: emit all values under a single "total" key.
class TotalMapper implements Mapper<string, number, string, number> {
  static runs = 0;
  mapEntry(_key: string, values: Values<number>, _ctx: Context): Iterable<[string, number]> {
    TotalMapper.runs += 1;
    log("mapper:total run", TotalMapper.runs);
    return values.toArray().map((v) => ["total", v]);
  }
}

// Reducer for sum: correctly implements add/remove.
class SumReducer implements Reducer<number, number> {
  static runsAdd = 0;
  static runsRemove = 0;
  initial: number | null = 0;
  add(acc: number | null, value: number): number {
    SumReducer.runsAdd += 1;
    log("reducer:sum add", SumReducer.runsAdd);
    return (acc ?? 0) + value;
  }
  remove(acc: number, value: number): number | null {
    SumReducer.runsRemove += 1;
    log("reducer:sum remove", SumReducer.runsRemove);
    return acc - value;
  }
}

class NumbersResource implements Resource<Collections> {
  instantiate(collections: Collections): EagerCollection<string, number> {
    return collections.numbers;
  }
}

class DoubledResource implements Resource<Collections> {
  instantiate(collections: Collections): EagerCollection<string, number> {
    return collections.numbers.map(DoubleMapper);
  }
}

class SumResource implements Resource<Collections> {
  instantiate(collections: Collections): EagerCollection<string, number> {
    return collections.numbers.map(TotalMapper).reduce(SumReducer);
  }
}

export const service: SkipService = {
  initialData: {
    numbers: [
      ["a", [1]],
      ["b", [2]],
      ["c", [3]],
      ["d", [4]],
      ["e", [5]],
      ["f", [6]],
      ["g", [7]],
      ["h", [8]],
      ["i", [9]],
      ["j", [10]],
    ],
  },
  resources: {
    numbers: NumbersResource,
    doubled: DoubledResource,
    sum: SumResource,
  },
  createGraph: (inputs) => inputs,
};

export const resetRunStats = () => {
  DoubleMapper.runs = 0;
  TotalMapper.runs = 0;
  SumReducer.runsAdd = 0;
  SumReducer.runsRemove = 0;
};

export const getRunStats = () => ({
  doubledMapperRuns: DoubleMapper.runs,
  totalMapperRuns: TotalMapper.runs,
  sumAddRuns: SumReducer.runsAdd,
  sumRemoveRuns: SumReducer.runsRemove,
});
