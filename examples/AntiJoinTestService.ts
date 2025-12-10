/**
 * AntiJoinTestService - Tests if Skip tracks dependencies on missing keys
 * 
 * This tests whether anti-join (set difference) can be expressed via map-with-lookup.
 * 
 * The key question: when a mapper looks up a key that doesn't exist in another
 * collection, does Skip track this as a dependency? If R2 later gains that key,
 * does the mapper re-run?
 * 
 * Setup:
 * - left: collection of entries we want to filter
 * - right: collection of "blocking" entries
 * - antiJoin: entries from left whose key has NO match in right
 * 
 * Test:
 * 1. left = {a: "value_a", b: "value_b"}
 * 2. right = {} (empty)
 * 3. antiJoin should be {a: "value_a", b: "value_b"} (nothing blocked)
 * 4. Add right = {a: "blocker"}
 * 5. antiJoin should become {b: "value_b"} (a is now blocked)
 * 
 * If step 5 works, Skip tracks negative dependencies and anti-join IS expressible!
 */

import {
  type Context,
  type EagerCollection,
  type Mapper,
  type Resource,
  type SkipService,
  type Values,
} from "@skipruntime/core";

type Entry = { value: string };
type Blocker = { reason: string };

type InputCollections = {
  left: EagerCollection<string, Entry>;
  right: EagerCollection<string, Blocker>;
};

type OutputCollections = {
  left: EagerCollection<string, Entry>;
  right: EagerCollection<string, Blocker>;
  antiJoin: EagerCollection<string, Entry>;
};

// Mapper that implements anti-join: keep left entries with no matching right key
class AntiJoinMapper implements Mapper<string, Entry, string, Entry> {
  constructor(private right: EagerCollection<string, Blocker>) {}

  mapEntry(
    key: string,
    values: Values<Entry>,
    _ctx: Context
  ): Iterable<[string, Entry]> {
    // Look up if this key exists in the "right" (blocking) collection
    const blockers = this.right.getArray(key);
    
    console.log(`[AntiJoinMapper] key=${key}, blockers.length=${blockers.length}`);
    
    if (blockers.length === 0) {
      // No blocker found - keep all entries for this key
      return values.toArray().map(v => [key, v] as [string, Entry]);
    } else {
      // Blocker exists - filter out this key
      return [];
    }
  }
}

// Resources
class LeftResource implements Resource<OutputCollections> {
  instantiate(collections: OutputCollections): EagerCollection<string, Entry> {
    return collections.left;
  }
}

class RightResource implements Resource<OutputCollections> {
  instantiate(collections: OutputCollections): EagerCollection<string, Blocker> {
    return collections.right;
  }
}

class AntiJoinResource implements Resource<OutputCollections> {
  instantiate(collections: OutputCollections): EagerCollection<string, Entry> {
    return collections.antiJoin;
  }
}

// The service definition
export const service: SkipService<InputCollections, OutputCollections> = {
  initialData: {
    left: [
      ["a", [{ value: "value_a" }]],
      ["b", [{ value: "value_b" }]],
    ],
    right: [],  // Initially empty - nothing blocked
  },

  resources: {
    left: LeftResource,
    right: RightResource,
    antiJoin: AntiJoinResource,
  },

  createGraph(inputs: InputCollections): OutputCollections {
    // The anti-join: left entries with no matching key in right
    const antiJoin = inputs.left.map(AntiJoinMapper, inputs.right);

    return {
      left: inputs.left,
      right: inputs.right,
      antiJoin,
    };
  },
};

