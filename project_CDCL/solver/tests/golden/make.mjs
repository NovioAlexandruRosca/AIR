// Records the Rust solver's answers (from `cdcl serve --port 8090`, the
// `rust` branch) for a fixed set of requests: tests/golden/cases.json.
// The TypeScript port must answer the same (tests/golden.test.ts).
//
//   node tests/golden/make.mjs [http://127.0.0.1:8090]

import { readdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const base = process.argv[2] ?? "http://127.0.0.1:8090";
const examples = join(here, "../../../examples/smt");

const post = async (endpoint, body) => (await fetch(`${base}/api/${endpoint}`, { method: "POST", body })).text();
const pgBody = (actions, lemmas, opts, src) =>
  `DECISIONS ${actions.join(" ")}\nLEMMAS ${lemmas.map((c) => c.join(" ") + " 0").join(" ")}\nOPTIONS ${opts.join(" ")}\n${src}`;

const cases = [];
const add = async (name, endpoint, body) => {
  const response = await post(endpoint, body);
  cases.push({ name, endpoint, body, response });
  return response;
};

/** Walk a few steps as a user would: pick the first unit clause, else decide the first open atom. */
async function walk(name, src, sign) {
  const actions = [];
  for (let step = 0; step < 6; step++) {
    const r = JSON.parse(await add(`${name} walk${sign > 0 ? "+" : "-"} ${step}`, "playground", pgBody(actions, [], [], src)));
    const rp = r.replay;
    if (!rp) return;
    if (rp.outcome === "units" && rp.units.length) actions.push(`u${rp.units[0].lit}`);
    else if ((rp.outcome === "open" || rp.outcome === "split") && rp.open?.length) actions.push(String(sign * rp.open[0]));
    else if (rp.outcome === "split" && rp.split) actions.push(String(rp.split.lit ?? rp.split));
    else return;
  }
}

const BOOL = [
  ["bool-chain", "(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)(declare-const s Bool)\n(assert (or (not p) q))(assert (or (not q) r))(assert (or (not p) (not r) s))"],
  ["bool-conflict", "(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)(declare-const s Bool)\n(assert (or (not p) q))(assert (or (not p) r))(assert (or (not q) (not r) (not s)))"],
  ["bool-uip", "(declare-const p Bool)(declare-const q Bool)(declare-const a Bool)(declare-const b Bool)(declare-const c Bool)(declare-const d Bool)\n(assert (or (not a) b))(assert (or (not b) (not p) c))(assert (or (not b) d))(assert (or (not c) (not d) (not q)))"],
];

const CNF = [
  ["cnf-small", "p cnf 3 4\n1 2 0\n-1 3 0\n-2 -3 0\n1 -3 0\n"],
  ["cnf-unsat", "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n"],
  ["cnf-php43", (() => {
    // pigeonhole: 4 pigeons, 3 holes (unsat)
    const v = (p, h) => p * 3 + h + 1;
    const cl = [];
    for (let p = 0; p < 4; p++) cl.push([0, 1, 2].map((h) => v(p, h)));
    for (let h = 0; h < 3; h++) for (let a = 0; a < 4; a++) for (let b = a + 1; b < 4; b++) cl.push([-v(a, h), -v(b, h)]);
    return `p cnf 12 ${cl.length}\n` + cl.map((c) => c.join(" ") + " 0").join("\n") + "\n";
  })()],
  ["cnf-random", (() => {
    let s = 12345;
    const rnd = () => ((s = (s * 1103515245 + 12345) % 2147483648), s);
    const cl = [];
    for (let i = 0; i < 170; i++) cl.push([0, 1, 2].map(() => (rnd() % 40 + 1) * (rnd() % 2 ? 1 : -1)));
    return `p cnf 40 ${cl.length}\n` + cl.map((c) => c.join(" ") + " 0").join("\n") + "\n";
  })()],
];

for (const f of readdirSync(examples).filter((f) => f.endsWith(".smt2")).sort()) {
  const src = readFileSync(join(examples, f), "utf8");
  const name = f.replace(/\.smt2$/, "");
  await add(`${name} solve`, "solve", src);
  await add(`${name} start`, "playground", pgBody([], [], [], src));
  await add(`${name} finish`, "playground", pgBody([], [], ["finish"], src));
  await add(`${name} finish-no-tp`, "playground", pgBody([], [], ["no-theory-propagation", "finish"], src));
  await walk(name, src, 1);
  await walk(name, src, -1);
}
for (const [name, src] of BOOL) {
  await add(`${name} solve`, "solve", src);
  await walk(name, src, 1);
  await walk(name, src, -1);
}
for (const [name, src] of CNF) await add(`${name} solve`, "solve", src);
await add("error smt", "solve", "(declare-const x Int)\n(assert (> x");
await add("error playground", "playground", "no decisions line\n(assert true)");
await add("error sort", "solve", "(declare-const x Int)\n(assert (and x true))");

writeFileSync(join(here, "cases.json"), JSON.stringify(cases, null, 1));
console.log(`${cases.length} cases`);
