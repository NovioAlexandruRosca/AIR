// Web Worker running the solver off the page's main thread. The page sends
// { id, endpoint, body } (what it used to POST to /api/<endpoint>) and gets
// back { id, text }: the JSON text the server answered with.

import { api_playground, api_solve } from "./api";

interface Request {
  id: number;
  endpoint: "solve" | "playground";
  body: string;
}

const scope = self as unknown as { onmessage: ((e: MessageEvent<Request>) => void) | null; postMessage: (m: unknown) => void };

scope.onmessage = (e) => {
  const { id, endpoint, body } = e.data;
  const text = endpoint === "solve" ? api_solve(body) : api_playground(body);
  scope.postMessage({ id, text });
};
