// Service for harness: one input, derived resources using mapper/reducer.
import {
  type Context,
  type EagerCollection,
  type Mapper,
  type Reducer,
  type Resource,
  type Values,
  type SkipService,
} from "@skipruntime/core";

const ENABLE_LOGS = process.env["SKIP_HARNESS_LOGS"] === "1";
const log = (...args: unknown[]) => {
  if (ENABLE_LOGS) console.log(...args);
};

type Collections = {
  numbers: EagerCollection<string, number>;
  edges: EagerCollection<string, [string, string]>;
  nodes: EagerCollection<string, string>;
  roots: EagerCollection<string, string>;
  graphState: EagerCollection<string, GraphState>;
  deadNodes: EagerCollection<string, string[]>;
};

type GraphValue =
  | { kind: "edge"; from: string; to: string }
  | { kind: "node"; id: string }
  | { kind: "root"; id: string };

type GraphState = {
  nodes: string[];
  roots: string[];
  reachable: string[];
  edgesOut: Record<string, string[]>;
  incoming: Record<string, number>;
};

// Utilities for graph state manipulation (JSON-friendly in the accumulator; Sets/Maps for computation).
const toSets = (state: GraphState) => {
  const nodes = new Set(state.nodes);
  const roots = new Set(state.roots);
  const reachable = new Set(state.reachable);
  const edgesOut = new Map<string, Set<string>>();
  for (const [k, vs] of Object.entries(state.edgesOut)) {
    edgesOut.set(k, new Set(vs));
  }
  const incoming = new Map<string, number>();
  for (const [k, v] of Object.entries(state.incoming)) {
    incoming.set(k, v);
  }
  return { nodes, roots, reachable, edgesOut, incoming };
};

const fromSets = (s: ReturnType<typeof toSets>): GraphState => ({
  nodes: Array.from(s.nodes),
  roots: Array.from(s.roots),
  reachable: Array.from(s.reachable),
  edgesOut: Object.fromEntries(Array.from(s.edgesOut.entries()).map(([k, vs]) => [k, Array.from(vs)])),
  incoming: Object.fromEntries(Array.from(s.incoming.entries())),
});

const ensureNode = (s: ReturnType<typeof toSets>, id: string) => {
  s.nodes.add(id);
  if (!s.edgesOut.has(id)) s.edgesOut.set(id, new Set());
  if (!s.incoming.has(id)) s.incoming.set(id, 0);
};

const propagateReachable = (s: ReturnType<typeof toSets>, start: string[]) => {
  const queue = [...start];
  while (queue.length > 0) {
    const u = queue.pop() as string;
    if (s.reachable.has(u)) continue;
    s.reachable.add(u);
    const outs = s.edgesOut.get(u);
    if (!outs) continue;
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

const propagateUnreachable = (s: ReturnType<typeof toSets>, start: string[]) => {
  const queue = [...start];
  while (queue.length > 0) {
    const u = queue.pop() as string;
    if (!s.reachable.has(u)) continue;
    if (s.roots.has(u)) continue; // roots stay reachable
    const incoming = s.incoming.get(u) ?? 0;
    if (incoming > 0) continue;
    s.reachable.delete(u);
    const outs = s.edgesOut.get(u);
    if (!outs) continue;
    for (const v of outs) {
      const newCount = Math.max(0, (s.incoming.get(v) ?? 0) - 1);
      s.incoming.set(v, newCount);
      if (newCount === 0 && !s.roots.has(v)) {
        queue.push(v);
      }
    }
  }
};

class GraphReducer implements Reducer<GraphValue, GraphState> {
  initial: GraphState | null = {
    nodes: [],
    roots: [],
    reachable: [],
    edgesOut: {},
    incoming: {},
  };

  add(acc: GraphState | null, value: GraphValue): GraphState {
    const state = toSets(acc ?? this.initial!);
    if (value.kind === "node") {
      ensureNode(state, value.id);
    } else if (value.kind === "root") {
      ensureNode(state, value.id);
      if (!state.roots.has(value.id)) {
        state.roots.add(value.id);
        propagateReachable(state, [value.id]);
      }
    } else {
      ensureNode(state, value.from);
      ensureNode(state, value.to);
      const outs = state.edgesOut.get(value.from)!;
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

  remove(acc: GraphState, value: GraphValue): GraphState | null {
    const state = toSets(acc ?? this.initial!);
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
    } else if (value.kind === "root") {
      state.roots.delete(value.id);
      if (state.roots.has(value.id)) {
        // no-op if still a root via another contribution
      } else if (state.reachable.has(value.id)) {
        // Remove reachability if no other incoming
        if ((state.incoming.get(value.id) ?? 0) === 0) {
          propagateUnreachable(state, [value.id]);
        }
      }
    } else {
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

class EdgeToGraphMapper implements Mapper<string, [string, string], string, GraphValue> {
  mapEntry(_key: string, values: Values<[string, string]>, _ctx: Context): Iterable<[string, GraphValue]> {
    return values.toArray().map(([from, to]) => ["graph", { kind: "edge", from, to }]);
  }
}

class NodeToGraphMapper implements Mapper<string, string, string, GraphValue> {
  mapEntry(_key: string, values: Values<string>, _ctx: Context): Iterable<[string, GraphValue]> {
    return values.toArray().map((id) => ["graph", { kind: "node", id }]);
  }
}

class RootToGraphMapper implements Mapper<string, string, string, GraphValue> {
  mapEntry(_key: string, values: Values<string>, _ctx: Context): Iterable<[string, GraphValue]> {
    return values.toArray().map((id) => ["graph", { kind: "root", id }]);
  }
}

// Mapper: multiply numeric values by 2, keep the same key.
class DoubleMapper implements Mapper<string, number, string, number> {
  static runs = 0;
  mapEntry(key: string, values: Values<number>, _ctx: Context): Iterable<[string, number]> {
    DoubleMapper.runs += 1;
    log("mapper:doubled run", DoubleMapper.runs, "key", key);
    const n = values.getUnique();
    return [[key, n * 2]];
  }
}

// Mapper for sum: emit all values under a single "total" key.
class TotalMapper implements Mapper<string, number, string, number> {
  static runs = 0;
  mapEntry(_key: string, values: Values<number>, _ctx: Context): Iterable<[string, number]> {
    TotalMapper.runs += 1;
    log("mapper:total run", TotalMapper.runs);
    return values.toArray().map((v) => ["total", v]);
  }
}

// Reducer for sum: correctly implements add/remove.
class SumReducer implements Reducer<number, number> {
  static runsAdd = 0;
  static runsRemove = 0;
  initial: number | null = 0;
  add(acc: number | null, value: number): number {
    SumReducer.runsAdd += 1;
    log("reducer:sum add", SumReducer.runsAdd);
    return (acc ?? 0) + value;
  }
  remove(acc: number, value: number): number | null {
    SumReducer.runsRemove += 1;
    log("reducer:sum remove", SumReducer.runsRemove);
    return acc - value;
  }
}

class NumbersResource implements Resource<Collections> {
  instantiate(collections: Collections): EagerCollection<string, number> {
    return collections.numbers;
  }
}

class DoubledResource implements Resource<Collections> {
  instantiate(collections: Collections): EagerCollection<string, number> {
    return collections.numbers.map(DoubleMapper);
  }
}

class SumResource implements Resource<Collections> {
  instantiate(collections: Collections): EagerCollection<string, number> {
    return collections.numbers.map(TotalMapper).reduce(SumReducer);
  }
}

class DeadNodesResource implements Resource<Collections> {
  instantiate(collections: Collections): EagerCollection<string, string[]> {
    // Map graph state to dead-node list: nodes minus reachable.
    class DeadMapper implements Mapper<string, GraphState, string, string[]> {
      mapEntry(key: string, values: Values<GraphState>, _ctx: Context): Iterable<[string, string[]]> {
        const state = values.getUnique();
        const reachable = new Set(state.reachable);
        const dead = state.nodes.filter((n) => !reachable.has(n));
        return [[key, dead]];
      }
    }
    return collections.graphState.map(DeadMapper);
  }
}

export const service: SkipService = {
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
    deadNodes: graphState.map(
      class DeadMapper implements Mapper<string, GraphState, string, string[]> {
        mapEntry(key: string, values: Values<GraphState>, _ctx: Context): Iterable<[string, string[]]> {
          const state = values.getUnique();
          const reachable = new Set(state.reachable);
          const dead = state.nodes.filter((n) => !reachable.has(n));
          return [[key, dead]];
        }
      },
    ),
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
