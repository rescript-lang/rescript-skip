// Mapper: multiply numeric values by 2, keep the same key.
class DoubleMapper {
    mapEntry(key, values) {
        const n = values.getUnique();
        return [[key, typeof n === "number" ? n * 2 : n]];
    }
}
// Mapper: emit all values under a single "total" key for reduction.
class TotalMapper {
    mapEntry(_key, values) {
        return values.toArray().map((v) => ["total", v]);
    }
}
// Reducer: sum numbers with seed 0.
class SumReducer {
    constructor() {
        this.initial = 0;
    }
    add(acc, value) {
        const a = typeof acc === "number" ? acc : 0;
        const n = typeof value === "number" ? value : 0;
        return a + n;
    }
    remove(acc, _value) {
        return acc;
    }
}
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
        ],
    },
    resources: {
        numbers: NumbersResource,
        doubled: DoubledResource,
        sum: SumResource,
    },
    createGraph: (inputs) => inputs,
};
