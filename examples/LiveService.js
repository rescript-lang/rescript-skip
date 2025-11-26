// Minimal echo resource used by LiveClient: mirrors the input collection.
class EchoResource {
    constructor(_params) { }
    instantiate(collections) {
        return collections.input;
    }
}
export const service = {
    initialData: {
        input: [["foo", ["bar"]]],
    },
    resources: {
        echo: EchoResource,
    },
    createGraph: (inputs) => inputs,
};
