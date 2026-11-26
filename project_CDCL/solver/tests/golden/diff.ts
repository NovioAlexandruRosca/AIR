// Show where the TypeScript answer differs from the recorded Rust answer.
//   npx tsx tests/golden/diff.ts "<case name>" ...
import { readFileSync } from "node:fs";
import { api_playground, api_solve } from "../../src/api";

interface Case {
  name: string;
  endpoint: string;
  body: string;
  response: string;
}
const cases: Case[] = JSON.parse(readFileSync(new URL("./cases.json", import.meta.url), "utf8"));
const names = process.argv.slice(2);
for (const c of cases.filter((c) => names.includes(c.name))) {
  const got = c.endpoint === "solve" ? api_solve(c.body) : api_playground(c.body);
  const a = JSON.parse(got);
  const b = JSON.parse(c.response);
  delete a.timing;
  delete b.timing;
  const out: string[] = [];
  const walk = (x: unknown, y: unknown, p: string) => {
    if (out.length > 8 || JSON.stringify(x) === JSON.stringify(y)) return;
    if (x && y && typeof x === "object" && typeof y === "object") {
      const xo = x as Record<string, unknown>;
      const yo = y as Record<string, unknown>;
      for (const k of new Set([...Object.keys(xo), ...Object.keys(yo)])) walk(xo[k], yo[k], `${p}.${k}`);
    } else out.push(`${p}:\n  ts   = ${JSON.stringify(x)?.slice(0, 400)}\n  rust = ${JSON.stringify(y)?.slice(0, 400)}`);
  };
  walk(a, b, "");
  console.log(`== ${c.name}\n${out.join("\n")}`);
}
