// The TypeScript solver must answer every recorded request exactly like the
// Rust solver did (tests/golden/cases.json, made by tests/golden/make.mjs on
// the `rust` branch). Only wall-clock timings may differ.

import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import { api_playground, api_solve } from "../src/api";

interface Case {
  name: string;
  endpoint: "solve" | "playground";
  body: string;
  response: string;
}

const cases: Case[] = JSON.parse(readFileSync(new URL("./golden/cases.json", import.meta.url), "utf8"));

/**
 * Drop what depends on the clock. The DT snapshot's "history" is compared
 * as a set: the Rust solver writes some of its entries in HashMap order,
 * which changes from run to run (dt.rs, "last constructor" step).
 */
function clean(x: unknown): unknown {
  if (Array.isArray(x)) return x.map(clean);
  if (x && typeof x === "object") {
    const out: Record<string, unknown> = {};
    for (const [k, v] of Object.entries(x))
      if (k === "history" && Array.isArray(v)) out[k] = v.map(clean).sort((p, q) => (JSON.stringify(p) < JSON.stringify(q) ? -1 : 1));
      else if (k !== "timing") out[k] = clean(v);
    return out;
  }
  return x;
}

describe("same answers as the Rust solver", () => {
  for (const c of cases)
    it(c.name, () => {
      const got = c.endpoint === "solve" ? api_solve(c.body) : api_playground(c.body);
      expect(clean(JSON.parse(got))).toEqual(clean(JSON.parse(c.response)));
    });
});
