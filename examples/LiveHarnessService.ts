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
  perKeySums: EagerCollection<string, number>;
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

// Mapper for naive sum: emit all values under a single "total" key.
class TotalMapperNaive implements Mapper<string, number, string, number> {
  static runs = 0;
  mapEntry(_key: string, values: Values<number>, _ctx: Context): Iterable<[string, number]> {
    TotalMapperNaive.runs += 1;
    log("mapper:totalNaive run", TotalMapperNaive.runs);
    return values.toArray().map((v) => ["total", v]);
  }
}

// Reducer for naive sum: forces recompute on removals.
class SumReducerNaive implements Reducer<number, number> {
  static runsAdd = 0;
  static runsRemove = 0;
  initial: number | null = 0;
  add(acc: number | null, value: number): number {
    SumReducerNaive.runsAdd += 1;
    log("reducer:sumNaive add", SumReducerNaive.runsAdd);
    return (acc ?? 0) + value;
  }
  remove(_acc: number, _value: number): number | null {
    SumReducerNaive.runsRemove += 1;
    log("reducer:sumNaive remove", SumReducerNaive.runsRemove);
    // Signal full recompute from scratch.
    return null;
  }
}

// Mapper for incremental sum: same shape as naive, separate counters.
class TotalMapperInc implements Mapper<string, number, string, number> {
  static runs = 0;
  mapEntry(_key: string, values: Values<number>, _ctx: Context): Iterable<[string, number]> {
    TotalMapperInc.runs += 1;
    log("mapper:totalInc run", TotalMapperInc.runs);
    return values.toArray().map((v) => ["total", v]);
  }
}

// Reducer for incremental sum: updates accumulator via add/remove.
class SumReducerInc implements Reducer<number, number> {
  static runsAdd = 0;
  static runsRemove = 0;
  initial: number | null = 0;
  add(acc: number | null, value: number): number {
    SumReducerInc.runsAdd += 1;
    log("reducer:sumInc add", SumReducerInc.runsAdd);
    return (acc ?? 0) + value;
  }
  remove(acc: number, value: number): number | null {
    SumReducerInc.runsRemove += 1;
    log("reducer:sumInc remove", SumReducerInc.runsRemove);
    // Purely incremental: adjust by delta.
    return acc - value;
  }
}

// Reducer for per-key sum: one accumulator per input key.
class PerKeySumReducer implements Reducer<number, number> {
  static runsAdd = 0;
  static runsRemove = 0;
  initial: number | null = 0;
  add(acc: number | null, value: number): number {
    PerKeySumReducer.runsAdd += 1;
    log("reducer:perKeySum add", PerKeySumReducer.runsAdd);
    return (acc ?? 0) + value;
  }
  remove(acc: number, value: number): number | null {
    PerKeySumReducer.runsRemove += 1;
    log("reducer:perKeySum remove", PerKeySumReducer.runsRemove);
    return acc - value;
  }
}

// Mapper: collapse per-key sums under a single "total" key.
class ToTotalMapper implements Mapper<string, number, string, number> {
  static runs = 0;
  mapEntry(_key: string, values: Values<number>, _ctx: Context): Iterable<[string, number]> {
    ToTotalMapper.runs += 1;
    log("mapper:toTotal run", ToTotalMapper.runs);
    const v = values.getUnique();
    return [["total", v]];
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

class PerKeySumResource implements Resource<Collections> {
  instantiate(collections: Collections): EagerCollection<string, number> {
    return collections.perKeySums;
  }
}

class SumNaiveResource implements Resource<Collections> {
  instantiate(collections: Collections): EagerCollection<string, number> {
    return collections.numbers.map(TotalMapperNaive).reduce(SumReducerNaive);
  }
}

class SumIncResource implements Resource<Collections> {
  instantiate(collections: Collections): EagerCollection<string, number> {
    return collections.numbers.map(TotalMapperInc).reduce(SumReducerInc);
  }
}

class SumOfPerKeySumsResource implements Resource<Collections> {
  instantiate(collections: Collections): EagerCollection<string, number> {
    return collections.perKeySums.map(ToTotalMapper).reduce(SumReducerInc);
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
    perKeySums: PerKeySumResource,
    sumNaive: SumNaiveResource,
    sumInc: SumIncResource,
    sumOfPerKeySums: SumOfPerKeySumsResource,
  },
  createGraph: (inputs) => {
    const perKeySums = inputs.numbers.reduce(PerKeySumReducer);
    return { ...inputs, perKeySums };
  },
};

export const resetRunStats = () => {
  DoubleMapper.runs = 0;
  TotalMapperNaive.runs = 0;
  SumReducerNaive.runsAdd = 0;
  SumReducerNaive.runsRemove = 0;
  TotalMapperInc.runs = 0;
  SumReducerInc.runsAdd = 0;
  SumReducerInc.runsRemove = 0;
  PerKeySumReducer.runsAdd = 0;
  PerKeySumReducer.runsRemove = 0;
  ToTotalMapper.runs = 0;
};

export const getRunStats = () => ({
  doubledMapperRuns: DoubleMapper.runs,
  totalNaiveMapperRuns: TotalMapperNaive.runs,
  sumNaiveAddRuns: SumReducerNaive.runsAdd,
  sumNaiveRemoveRuns: SumReducerNaive.runsRemove,
  totalIncMapperRuns: TotalMapperInc.runs,
  sumIncAddRuns: SumReducerInc.runsAdd,
  sumIncRemoveRuns: SumReducerInc.runsRemove,
  perKeySumAddRuns: PerKeySumReducer.runsAdd,
  perKeySumRemoveRuns: PerKeySumReducer.runsRemove,
  toTotalMapperRuns: ToTotalMapper.runs,
});
