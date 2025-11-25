// Minimal SkipService definition in JS for live runtime testing.
class EchoResource {
  constructor(_params) {}
  instantiate(collections, _context) {
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
  createGraph: (inputs, _ctx) => inputs,
};
