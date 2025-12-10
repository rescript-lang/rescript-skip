// Identity resource: exposes allKeys so we can observe its key order.
class AllKeysResource {
    constructor(_params) { }
    instantiate(collections) {
        return collections.allKeys;
    }
}
// Slice resource: restrict keys to a mid-range in Json order.
// We slice from false (booleans) up through strings.
class SliceResource {
    constructor(_params) { }
    instantiate(collections) {
        // false < true < numbers < strings in Json ordering.
        return collections.allKeys.slice(false, "zzzz");
    }
}
// Take resource: keep only the first few entries in Json order.
class TakeResource {
    constructor(_params) { }
    instantiate(collections) {
        return collections.allKeys.take(5);
    }
}
// Slices resource: keep two disjoint ranges using slices([...]).
class SlicesResource {
    constructor(_params) { }
    instantiate(collections) {
        return collections.allKeys.slices([false, true], // booleans
        ["", "zzzz"]);
    }
}
// Merge resource: union of leftKeys and rightKeys to exercise merge semantics.
class MergedKeysResource {
    constructor(_params) { }
    instantiate(collections) {
        return collections.leftKeys.merge(collections.rightKeys);
    }
}
// Helper to label entries for easier inspection.
const label = (kind, desc) => `${kind}:${desc}`;
export const service = {
    initialData: {
        // Keys spanning all Json shapes we can write directly in this TS service.
        // (Top-level `null` keys are added from the ReScript harness.)
        //
        // SERIALIZATION (discovered empirically):
        // - Booleans are converted to numbers in output: false->0, true->1
        // - This happens recursively in arrays and objects
        //
        // NO KEY COLLISION:
        // - Despite serialization, boolean keys do NOT collide with numeric 0/1
        // - The runtime preserves identity: false and 0 coexist (both serialize as 0)
        // - Same for nested: [false] and [0] coexist, {x:false} and {x:0} coexist
        //
        // ORDER (observed):
        // - null < booleans (as 0,1) < negative numbers < non-negative numbers < strings < arrays < objects
        // - Booleans come BEFORE all actual numbers, even negatives
        // - Example: 0(bool) < 1(bool) < -100 < -1 < 0(num) < 1(num) < 100
        // - Strings: lexicographic
        // - Arrays/objects: lexicographic by elements/key-value pairs
        allKeys: [
            // === Test 1: Boolean/number NO collision ===
            // Both booleans and their numeric equivalents coexist as separate keys
            [false, [label("bool", "false")]],
            [true, [label("bool", "true")]],
            [0, [label("num", "0")]], // distinct from false (no collision)
            [1, [label("num", "1")]], // distinct from true (no collision)
            // === Test 2: Other numbers (no collision) ===
            [-100, [label("num", "-100")]],
            [-1, [label("num", "-1")]],
            [-0.5, [label("num", "-0.5")]],
            [0.5, [label("num", "0.5")]],
            [1.5, [label("num", "1.5")]],
            [100, [label("num", "100")]],
            // === Test 3: Strings ===
            ["", [label("str", "empty")]],
            ["0", [label("str", "0")]], // string "0" - should NOT collide with number 0
            ["1", [label("str", "1")]], // string "1" - should NOT collide with number 1
            ["a", [label("str", "a")]],
            ["b", [label("str", "b")]],
            // === Test 4: Array NO collision ===
            // [false]/[true] coexist with [0]/[1] as separate keys
            [[false], [label("arr", "[false]")]],
            [[true], [label("arr", "[true]")]],
            [[0], [label("arr", "[0]")]], // distinct from [false]
            [[1], [label("arr", "[1]")]], // distinct from [true]
            // === Test 5: Other arrays (no collision) ===
            [[], [label("arr", "[]")]],
            [[-1], [label("arr", "[-1]")]],
            [[0, 0], [label("arr", "[0,0]")]],
            [[0, 1], [label("arr", "[0,1]")]],
            [["a"], [label("arr", "[a]")]],
            [[[]], [label("arr", "[[]]")]],
            // === Test 6: Object NO collision ===
            // {x:false}/{x:true} coexist with {x:0}/{x:1} as separate keys
            [{ x: false }, [label("obj", "{x:false}")]],
            [{ x: true }, [label("obj", "{x:true}")]],
            [{ x: 0 }, [label("obj", "{x:0}")]], // distinct from {x:false}
            [{ x: 1 }, [label("obj", "{x:1}")]], // distinct from {x:true}
            // === Test 7: Other objects (no collision) ===
            [{}, [label("obj", "{}")]],
            [{ a: 1 }, [label("obj", "{a:1}")]],
            [{ a: 1, b: 2 }, [label("obj", "{a:1,b:2}")]],
            [{ a: 2 }, [label("obj", "{a:2}")]],
            [{ b: 2 }, [label("obj", "{b:2}")]],
        ],
        // Left and right collections share some keys and differ on others
        // so that merge can be inspected.
        leftKeys: [
            [false, [label("left", "false")]],
            [0, [label("left", "0")]],
            ["a", [label("left", "a")]],
            [[], [label("left", "[]")]],
            [{ a: 1 }, [label("left", "{a:1}")]],
        ],
        rightKeys: [
            [true, [label("right", "true")]],
            [0, [label("right", "0")]], // overlap on 0
            ["b", [label("right", "b")]],
            [[0], [label("right", "[0]")]],
            [{ a: 1 }, [label("right", "{a:1}")]], // overlap on {a:1}
        ],
    },
    resources: {
        allKeys: AllKeysResource,
        allKeysSlice: SliceResource,
        allKeysTake: TakeResource,
        allKeysSlices: SlicesResource,
        mergedKeys: MergedKeysResource,
    },
    // No additional derived collections: createGraph is the identity on inputs.
    createGraph: (inputs) => inputs,
};
