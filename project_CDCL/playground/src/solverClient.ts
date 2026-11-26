// The solver runs in the browser, in Web Workers (solver/src/worker.ts), so
// a long solve never freezes the page. `call` sends what used to be the body
// of `POST /api/<endpoint>` and resolves with the JSON text answered.

type Endpoint = "solve" | "playground";

const POOL = 2; // previews are prefetched while the main request runs
const workers: Worker[] = [];
const pending = new Map<number, (text: string) => void>();
let nextId = 0;
let turn = 0;

function worker(): Worker {
  if (workers.length < POOL) {
    const w = new Worker(new URL("../../solver/src/worker.ts", import.meta.url), { type: "module" });
    w.onmessage = (e: MessageEvent<{ id: number; text: string }>) => {
      pending.get(e.data.id)?.(e.data.text);
      pending.delete(e.data.id);
    };
    workers.push(w);
    return w;
  }
  return workers[turn++ % workers.length];
}

export function call(endpoint: Endpoint, body: string): Promise<string> {
  const id = nextId++;
  return new Promise((resolve) => {
    pending.set(id, resolve);
    worker().postMessage({ id, endpoint, body });
  });
}
