import { type EagerCollection, type Resource, type SkipService } from "@skipruntime/core";

type Collections = {
  input: EagerCollection<string, string>;
};

// Minimal echo resource used by LiveClient: mirrors the input collection.
class EchoResource implements Resource<Collections> {
  constructor(_params: unknown) {}
  instantiate(collections: Collections): EagerCollection<string, string> {
    return collections.input;
  }
}

export const service: SkipService = {
  initialData: {
    input: [["foo", ["bar"]]],
  },
  resources: {
    echo: EchoResource,
  },
  createGraph: (inputs: Collections) => inputs,
};
