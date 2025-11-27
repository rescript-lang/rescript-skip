// End-to-end test of the graph/dead-code example using HTTP snapshots.
import { runService } from "@skipruntime/server";
import { service } from "./LiveHarnessService.js";

const CONTROL_PORT = 18090;
const STREAMING_PORT = 18091;
const HOST = `http://127.0.0.1:${CONTROL_PORT}`;

const postJSON = async (path, body) => {
  const res = await fetch(`${HOST}${path}`, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(body),
  });
  if (!res.ok) {
    throw new Error(`POST ${path} failed: ${res.status} ${await res.text()}`);
  }
  return res.json();
};

const patchJSON = async (path, body) => {
  const res = await fetch(`${HOST}${path}`, {
    method: "PATCH",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(body),
  });
  if (!res.ok) {
    throw new Error(`PATCH ${path} failed: ${res.status} ${await res.text()}`);
  }
  // Some PATCH responses have empty bodies; ignore the payload.
  return undefined;
};

const getDead = async () => {
  const snapshot = await postJSON("/v1/snapshot/dead", null);
  // snapshot is [ [ key, [deadList] ] ], key should be "graph"
  if (!Array.isArray(snapshot) || snapshot.length === 0) {
    throw new Error(`Unexpected dead snapshot shape: ${JSON.stringify(snapshot)}`);
  }
  const entry = snapshot[0];
  const values = entry[1];
  const deadList = Array.isArray(values) && values.length > 0 && Array.isArray(values[0]) ? values[0] : [];
  return deadList.slice().sort();
};

const assertDead = (actual, expected, label) => {
  const a = actual.slice().sort();
  const e = expected.slice().sort();
  if (a.length !== e.length || a.some((v, i) => v !== e[i])) {
    throw new Error(`${label}: expected dead=${JSON.stringify(e)}, got ${JSON.stringify(a)}`);
  }
  console.log(`${label}: OK -> dead=${JSON.stringify(a)}`);
};

const main = async () => {
  console.log("Starting LiveHarnessService on 18090/18091 for graph E2E test...");
  const server = await runService(service, {
    control_port: CONTROL_PORT,
    streaming_port: STREAMING_PORT,
    platform: "wasm",
  });
  try {
    // Baseline: only "unused" should be dead.
    const dead0 = await getDead();
    assertDead(dead0, ["unused"], "initial");

    // Drop util -> lib edge in fileA: lib and helper become unreachable.
    await patchJSON("/v1/inputs/edges", [
      ["fileA", [["main", "util"]]],
    ]);
    const dead1 = await getDead();
    assertDead(dead1, ["unused", "lib", "helper"], "after removing util→lib");

    // Reintroduce reachability via fileB: util -> lib.
    await patchJSON("/v1/inputs/edges", [
      ["fileB", [
        ["lib", "helper"],
        ["util", "lib"],
      ]],
    ]);
    const dead2 = await getDead();
    assertDead(dead2, ["unused"], "after adding util→lib in fileB");
  } finally {
    await server.close();
  }
};

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
