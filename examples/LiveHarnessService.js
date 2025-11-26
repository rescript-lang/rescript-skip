const ENABLE_LOGS = process.env["SKIP_HARNESS_LOGS"] === "1";
const log = (...args) => {
    if (ENABLE_LOGS)
        console.log(...args);
};
// Mapper: multiply numeric values by 2, keep the same key.
class DoubleMapper {
    mapEntry(key, values, _ctx) {
        DoubleMapper.runs += 1;
        log("mapper:doubled run", DoubleMapper.runs, "key", key);
        const n = values.getUnique();
        return [[key, n * 2]];
    }
}
DoubleMapper.runs = 0;
// Mapper for naive sum: emit all values under a single "total" key.
class TotalMapperNaive {
    mapEntry(_key, values, _ctx) {
        TotalMapperNaive.runs += 1;
        log("mapper:totalNaive run", TotalMapperNaive.runs);
        return values.toArray().map((v) => ["total", v]);
    }
}
TotalMapperNaive.runs = 0;
// Reducer for naive sum: forces recompute on removals.
class SumReducerNaive {
    constructor() {
        this.initial = 0;
    }
    add(acc, value) {
        SumReducerNaive.runsAdd += 1;
        log("reducer:sumNaive add", SumReducerNaive.runsAdd);
        return (acc ?? 0) + value;
    }
    remove(_acc, _value) {
        SumReducerNaive.runsRemove += 1;
        log("reducer:sumNaive remove", SumReducerNaive.runsRemove);
        // Signal full recompute from scratch.
        return null;
    }
}
SumReducerNaive.runsAdd = 0;
SumReducerNaive.runsRemove = 0;
// Mapper for incremental sum: same shape as naive, separate counters.
class TotalMapperInc {
    mapEntry(_key, values, _ctx) {
        TotalMapperInc.runs += 1;
        log("mapper:totalInc run", TotalMapperInc.runs);
        return values.toArray().map((v) => ["total", v]);
    }
}
TotalMapperInc.runs = 0;
// Reducer for incremental sum: updates accumulator via add/remove.
class SumReducerInc {
    constructor() {
        this.initial = 0;
    }
    add(acc, value) {
        SumReducerInc.runsAdd += 1;
        log("reducer:sumInc add", SumReducerInc.runsAdd);
        return (acc ?? 0) + value;
    }
    remove(acc, value) {
        SumReducerInc.runsRemove += 1;
        log("reducer:sumInc remove", SumReducerInc.runsRemove);
        // Purely incremental: adjust by delta.
        return acc - value;
    }
}
SumReducerInc.runsAdd = 0;
SumReducerInc.runsRemove = 0;
class NumbersResource {
    instantiate(collections) {
        return collections.numbers;
    }
}
class DoubledResource {
    instantiate(collections) {
        return collections.numbers.map(DoubleMapper);
    }
}
class SumNaiveResource {
    instantiate(collections) {
        return collections.numbers.map(TotalMapperNaive).reduce(SumReducerNaive);
    }
}
class SumIncResource {
    instantiate(collections) {
        return collections.numbers.map(TotalMapperInc).reduce(SumReducerInc);
    }
}
export const service = {
    initialData: {
        numbers: [
            ["a", [1]],
            ["b", [2]],
        ],
    },
    resources: {
        numbers: NumbersResource,
        doubled: DoubledResource,
        sumNaive: SumNaiveResource,
        sumInc: SumIncResource,
    },
    createGraph: (inputs) => inputs,
};
export const resetRunStats = () => {
    DoubleMapper.runs = 0;
    TotalMapperNaive.runs = 0;
    SumReducerNaive.runsAdd = 0;
    SumReducerNaive.runsRemove = 0;
    TotalMapperInc.runs = 0;
    SumReducerInc.runsAdd = 0;
    SumReducerInc.runsRemove = 0;
};
export const getRunStats = () => ({
    doubledMapperRuns: DoubleMapper.runs,
    totalNaiveMapperRuns: TotalMapperNaive.runs,
    sumNaiveAddRuns: SumReducerNaive.runsAdd,
    sumNaiveRemoveRuns: SumReducerNaive.runsRemove,
    totalIncMapperRuns: TotalMapperInc.runs,
    sumIncAddRuns: SumReducerInc.runsAdd,
    sumIncRemoveRuns: SumReducerInc.runsRemove,
});
