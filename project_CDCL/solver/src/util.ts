// Helpers shared by the port.

/**
 * `Err(e)` of a Rust `Result`: a function returning `Result<T, E>` returns T
 * and throws `new RustErr(e)` instead. Callers that matched on the error
 * catch it: `catch (x) { if (!(x instanceof RustErr)) throw x; ... x.value }`.
 */
export class RustErr<E = unknown> extends Error {
  constructor(public value: E) {
    super(typeof value === "string" ? value : value && typeof value === "object" && "message" in value ? String((value as { message: unknown }).message) : "error");
  }
}

/** `format!("{:.N}", x)` */
export const fixed = (x: number, n: number) => x.toFixed(n);

/** Milliseconds since some fixed point (Rust `Instant`). */
export const now = (): number => (typeof performance !== "undefined" ? performance.now() : Date.now());
