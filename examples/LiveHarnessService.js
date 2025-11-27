const ENABLE_LOGS = process.env["SKIP_HARNESS_LOGS"] === "1";
const log = (...args) => {
    if (ENABLE_LOGS)
        console.log(...args);
};
// Utilities for graph state manipulation (JSON-friendly in the accumulator; Sets/Maps for computation).
const toSets = (state) => {
    const nodes = new Set(state.nodes);
    const roots = new Set(state.roots);
    const reachable = new Set(state.reachable);
    const edgesOut = new Map();
    for (const [k, vs] of Object.entries(state.edgesOut)) {
        edgesOut.set(k, new Set(vs));
    }
    const incoming = new Map();
    for (const [k, v] of Object.entries(state.incoming)) {
        incoming.set(k, v);
    }
    return { nodes, roots, reachable, edgesOut, incoming };
};
const fromSets = (s) => ({
    nodes: Array.from(s.nodes),
    roots: Array.from(s.roots),
    reachable: Array.from(s.reachable),
    edgesOut: Object.fromEntries(Array.from(s.edgesOut.entries()).map(([k, vs]) => [k, Array.from(vs)])),
    incoming: Object.fromEntries(Array.from(s.incoming.entries())),
});
const ensureNode = (s, id) => {
    s.nodes.add(id);
    if (!s.edgesOut.has(id))
        s.edgesOut.set(id, new Set());
    if (!s.incoming.has(id))
        s.incoming.set(id, 0);
};
const propagateReachable = (s, start) => {
    const queue = [...start];
    while (queue.length > 0) {
        const u = queue.pop();
        if (s.reachable.has(u))
            continue;
        s.reachable.add(u);
        const outs = s.edgesOut.get(u);
        if (!outs)
            continue;
        for (const v of outs) {
            ensureNode(s, v);
            const newCount = (s.incoming.get(v) ?? 0) + 1;
            s.incoming.set(v, newCount);
            if (!s.reachable.has(v)) {
                queue.push(v);
            }
        }
    }
};
const propagateUnreachable = (s, start) => {
    const queue = [...start];
    while (queue.length > 0) {
        const u = queue.pop();
        if (!s.reachable.has(u))
            continue;
        if (s.roots.has(u))
            continue; // roots stay reachable
        const incoming = s.incoming.get(u) ?? 0;
        if (incoming > 0)
            continue;
        s.reachable.delete(u);
        const outs = s.edgesOut.get(u);
        if (!outs)
            continue;
        for (const v of outs) {
            const newCount = Math.max(0, (s.incoming.get(v) ?? 0) - 1);
            s.incoming.set(v, newCount);
            if (newCount === 0 && !s.roots.has(v)) {
                queue.push(v);
            }
        }
    }
};
class GraphReducer {
    constructor() {
        this.initial = {
            nodes: [],
            roots: [],
            reachable: [],
            edgesOut: {},
            incoming: {},
        };
    }
    add(acc, value) {
        const state = toSets(acc ?? this.initial);
        if (value.kind === "node") {
            ensureNode(state, value.id);
        }
        else if (value.kind === "root") {
            ensureNode(state, value.id);
            if (!state.roots.has(value.id)) {
                state.roots.add(value.id);
                propagateReachable(state, [value.id]);
            }
        }
        else {
            ensureNode(state, value.from);
            ensureNode(state, value.to);
            const outs = state.edgesOut.get(value.from);
            if (!outs.has(value.to)) {
                outs.add(value.to);
                if (state.reachable.has(value.from)) {
                    const newCount = (state.incoming.get(value.to) ?? 0) + 1;
                    state.incoming.set(value.to, newCount);
                    if (!state.reachable.has(value.to)) {
                        propagateReachable(state, [value.to]);
                    }
                }
            }
        }
        return fromSets(state);
    }
    remove(acc, value) {
        const state = toSets(acc ?? this.initial);
        if (value.kind === "node") {
            // Removing a node: drop from sets; edges incident to it are left intact for simplicity.
            state.nodes.delete(value.id);
            state.roots.delete(value.id);
            if (state.reachable.has(value.id)) {
                state.reachable.delete(value.id);
                propagateUnreachable(state, Array.from(state.edgesOut.get(value.id) ?? []));
            }
            state.edgesOut.delete(value.id);
            state.incoming.delete(value.id);
        }
        else if (value.kind === "root") {
            state.roots.delete(value.id);
            if (state.roots.has(value.id)) {
                // no-op if still a root via another contribution
            }
            else if (state.reachable.has(value.id)) {
                // Remove reachability if no other incoming
                if ((state.incoming.get(value.id) ?? 0) === 0) {
                    propagateUnreachable(state, [value.id]);
                }
            }
        }
        else {
            const outs = state.edgesOut.get(value.from);
            if (outs && outs.has(value.to)) {
                outs.delete(value.to);
                if (state.reachable.has(value.from)) {
                    const newCount = Math.max(0, (state.incoming.get(value.to) ?? 0) - 1);
                    state.incoming.set(value.to, newCount);
                    if (newCount === 0 && !state.roots.has(value.to)) {
                        propagateUnreachable(state, [value.to]);
                    }
                }
            }
        }
        return fromSets(state);
    }
}
class EdgeToGraphMapper {
    mapEntry(_key, values, _ctx) {
        return values.toArray().map(([from, to]) => ["graph", { kind: "edge", from, to }]);
    }
}
class NodeToGraphMapper {
    mapEntry(_key, values, _ctx) {
        return values.toArray().map((id) => ["graph", { kind: "node", id }]);
    }
}
class RootToGraphMapper {
    mapEntry(_key, values, _ctx) {
        return values.toArray().map((id) => ["graph", { kind: "root", id }]);
    }
}
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
class DeadNodesResource {
    instantiate(collections) {
        // Map graph state to dead-node list: nodes minus reachable.
        class DeadMapper {
            mapEntry(key, values, _ctx) {
                const state = values.getUnique();
                const reachable = new Set(state.reachable);
                const dead = state.nodes.filter((n) => !reachable.has(n));
                return [[key, dead]];
            }
        }
        return collections.graphState.map(DeadMapper);
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
        edges: [
            ["fileA", [
                    ["main", "util"],
                    ["util", "lib"],
                ]],
            ["fileB", [["lib", "helper"]]],
            ["fileC", []],
        ],
        nodes: [
            ["fileA", ["main", "util"]],
            ["fileB", ["lib", "helper"]],
            ["fileC", ["unused"]],
        ],
        roots: [
            ["fileA", ["main"]],
            ["fileB", []],
            ["fileC", []],
        ],
    },
    resources: {
        numbers: NumbersResource,
        doubled: DoubledResource,
        sum: SumResource,
        dead: DeadNodesResource,
    },
    createGraph: (inputs) => {
        const toGraphEdges = inputs.edges.map(EdgeToGraphMapper);
        const toGraphNodes = inputs.nodes.map(NodeToGraphMapper);
        const toGraphRoots = inputs.roots.map(RootToGraphMapper);
        const graphInputs = toGraphEdges.merge(toGraphNodes, toGraphRoots);
        const graphState = graphInputs.reduce(GraphReducer);
        return {
            ...inputs,
            graphInputs,
            graphState,
            deadNodes: graphState.map(class DeadMapper {
                mapEntry(key, values, _ctx) {
                    const state = values.getUnique();
                    const reachable = new Set(state.reachable);
                    const dead = state.nodes.filter((n) => !reachable.has(n));
                    return [[key, dead]];
                }
            }),
        };
    },
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
