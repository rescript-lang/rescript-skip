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
// Mapper for sum: emit all values under a single "total" key.
class TotalMapper {
    mapEntry(_key, values, _ctx) {
        TotalMapper.runs += 1;
        log("mapper:total run", TotalMapper.runs);
        return values.toArray().map((v) => ["total", v]);
    }
}
TotalMapper.runs = 0;
// Reducer for sum: correctly implements add/remove.
class SumReducer {
    constructor() {
        this.initial = 0;
    }
    add(acc, value) {
        SumReducer.runsAdd += 1;
        log("reducer:sum add", SumReducer.runsAdd);
        return (acc ?? 0) + value;
    }
    remove(acc, value) {
        SumReducer.runsRemove += 1;
        log("reducer:sum remove", SumReducer.runsRemove);
        return acc - value;
    }
}
SumReducer.runsAdd = 0;
SumReducer.runsRemove = 0;
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
class SumResource {
    instantiate(collections) {
        return collections.numbers.map(TotalMapper).reduce(SumReducer);
    }
}
export const service = {
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
