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
// Mapper that implements anti-join: keep left entries with no matching right key
class AntiJoinMapper {
    right;
    constructor(right) {
        this.right = right;
    }
    mapEntry(key, values, _ctx) {
        // Look up if this key exists in the "right" (blocking) collection
        const blockers = this.right.getArray(key);
        console.log(`[AntiJoinMapper] key=${key}, blockers.length=${blockers.length}`);
        if (blockers.length === 0) {
            // No blocker found - keep all entries for this key
            return values.toArray().map(v => [key, v]);
        }
        else {
            // Blocker exists - filter out this key
            return [];
        }
    }
}
// Resources
class LeftResource {
    instantiate(collections) {
        return collections.left;
    }
}
class RightResource {
    instantiate(collections) {
        return collections.right;
    }
}
class AntiJoinResource {
    instantiate(collections) {
        return collections.antiJoin;
    }
}
// The service definition
export const service = {
    initialData: {
        left: [
            ["a", [{ value: "value_a" }]],
            ["b", [{ value: "value_b" }]],
        ],
        right: [], // Initially empty - nothing blocked
    },
    resources: {
        left: LeftResource,
        right: RightResource,
        antiJoin: AntiJoinResource,
    },
    createGraph(inputs) {
        // The anti-join: left entries with no matching key in right
        const antiJoin = inputs.left.map(AntiJoinMapper, inputs.right);
        return {
            left: inputs.left,
            right: inputs.right,
            antiJoin,
        };
    },
};
