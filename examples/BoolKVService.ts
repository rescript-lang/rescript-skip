// Minimal service to test how booleans behave as keys and values.
import {
  type EagerCollection,
  type Resource,
  type SkipService,
} from "@skipruntime/core";

type Collections = {
  boolKV: EagerCollection<boolean, boolean>;
};

class BoolKVResource implements Resource<Collections> {
  constructor(_params: unknown) {}
  instantiate(collections: Collections): EagerCollection<boolean, boolean> {
    return collections.boolKV;
  }
}

export const service: SkipService = {
  initialData: {
    boolKV: [
      [false, [false]],
      [true, [true]],
    ],
  },
  resources: {
    boolKV: BoolKVResource,
  },
  createGraph: (inputs: Collections): Collections => inputs,
};

