# Porting conventions (Rust → TypeScript)

The TypeScript solver is a line-by-line port of the Rust crate (on the
`rust` branch: `src/`). Several files are ported in parallel, so
every file follows these rules; then a name used in one file is known in all
the others without coordination.

**Layout.** (Rust branch) `src/X.rs` → `solver/src/X.ts`, `src/smt/X.rs` → `solver/src/smt/X.ts`.
Relative imports without extension (`import { Terms } from "./term"`).
Unit tests (`#[cfg(test)] mod tests`) → `solver/tests/<name>.test.ts` (vitest:
`import { describe, it, expect } from "vitest"`).

**Names stay the Rust names, exactly.** Functions, methods, fields, constants
keep their snake_case / SCREAMING_CASE / CamelCase spelling. `pub` items are
exported. `Foo::new(..)` → `static new(..)` (call `Foo.new(..)`); other
associated functions → static methods with the same name.

**Structs** → classes with the same fields (public) and methods. Plain data
structs without methods may be `interface`s — but if *any* code calls
`Foo { .. }` / `Foo::new`, export a class so `new Foo(...)` or `Foo.new(...)`
works; prefer classes when unsure. `#[derive(Default)]` → fields have the
default values (0, false, [], null, new Map()) and the constructor takes no
arguments or an optional `Partial<Foo>`.

**Traits** → `export abstract class Trait` with the same methods; default
methods have their Rust bodies; required methods are `abstract`.
Implementors `extends Trait`. (`Theory` in smt/theory.ts, `TheoryHook` in
solver.ts.)

**Enums.**
- Only unit variants (C-like): string literal union of the variant names,
  `export type Status = "Sat" | "Unsat" | "Unknown";`
- With data: discriminated union on `kind`, one exported type per enum:
  - struct variant `V { a, b }` → `{ kind: "V"; a: A; b: B }`
  - tuple variant `V(x, y)` → `{ kind: "V"; _0: X; _1: Y }`
  - unit variant `V` → `{ kind: "V" }`
- Methods of an enum (`impl Status { fn as_str(self) }`) → exported functions
  `Status_as_str(s: Status)`; associated constructors likewise
  (`Value_int(..)` for `Value::int(..)`).

**Types.**
- `usize`, `u32`, `i32`, `i64`, `u64`, `f64` → `number`; `i128` → `bigint`.
- `Lit` → `number` from `lit.ts`: `Lit::new(v, pos)` → `lit_new(v, pos)`,
  `l.var()` → `lit_var(l)`, `!l` → `lit_not(l)`, `l.is_positive()` →
  `lit_is_positive(l)`, `l.index()` → `lit_index(l)`,
  `Lit::from_dimacs(x)` / `l.to_dimacs()` → `lit_from_dimacs` / `lit_to_dimacs`.
- `Option<T>` → `T | null` (never `undefined`).
- `Result<T, E>` → return `T`; `Err(e)` → `throw new RustErr(e)` (util.ts).
  `?` becomes plain propagation. Code that matches on `Err` catches
  `RustErr` and rethrows anything else.
- `Vec<T>` → `T[]`; `HashMap`/`BTreeMap` → `Map`; `HashSet`/`BTreeSet` → `Set`.
  For composite keys (tuples, Vecs) use a string key (`${a},${b}`) and note it.
  BTreeMap/BTreeSet iteration is sorted in Rust: sort the keys when iterating.
- `String`/`&str` → `string`; `char` → one-character string.
- `Instant` → `number` (ms from `now()` in util.ts), `Duration` → ms.
- `Arc<AtomicBool>` → `{ value: boolean }`.
- `&mut x` of a primitive that the callee writes → a `{ v: T }` box.
- `Box<dyn Fn..>` / `&dyn Fn` / `impl FnMut` → plain functions.

**Behaviour must be identical**: same algorithm, same iteration order, same
tie-breaking, same JSON text. Rust's `sort`/`sort_by` is stable, as is
`Array.prototype.sort`; for `sort_unstable*` use a stable sort as well (with
a comparator on the same key). `{:.4}` → `toFixed(4)`. JSON is built as
strings exactly like the Rust code (port `json_string` from trace.rs; don't
switch to `JSON.stringify` of objects). `{:?}` formatting that ends up in
output: reproduce what Rust prints.
Integer division `/` on integers → `Math.trunc(a / b)` (or bigint `/`,
which truncates); `%` behaves the same as Rust for numbers and bigints.

Don't add features, don't "improve" algorithms. Keep the Rust comments
(as `//` / `/** */`), they are the documentation.

**String writers.** Every Rust `out: &mut String` parameter (`json_string`,
`write_json`, snapshot helpers, …) becomes `out: { v: string }`, appended
with `out.v += ...`. Functions returning `String` still return a string.
