class BoolKVResource {
    constructor(_params) { }
    instantiate(collections) {
        return collections.boolKV;
    }
}
export const service = {
    initialData: {
        boolKV: [
            [false, [false]],
            [true, [true]],
        ],
    },
    resources: {
        boolKV: BoolKVResource,
    },
    createGraph: (inputs) => inputs,
};
