import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";

// A static site: `npm run build` writes ../dist (index.html, JS, CSS and the
// solver's worker). The solver runs in the browser, so any static host can
// serve it, from any sub-path (relative URLs).
export default defineConfig({
  plugins: [react()],
  base: "./",
  build: {
    outDir: "../dist",
    emptyOutDir: true,
    chunkSizeWarningLimit: 1500, // one bundle on purpose (three.js included)
  },
  worker: { format: "es" },
  server: {
    fs: { allow: [".."] }, // the examples (../examples/smt) and the solver (../solver)
  },
});
