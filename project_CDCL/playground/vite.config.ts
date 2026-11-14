import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";

// The build is embedded into the Rust binary (src/server.rs), so file names
// must be fixed: ui/playground/{index.html, playground.js, playground.css}.
export default defineConfig({
  plugins: [react()],
  base: "./",
  build: {
    outDir: "../ui/playground",
    emptyOutDir: true,
    cssCodeSplit: false,
    chunkSizeWarningLimit: 1500, // one bundle on purpose (three.js included)
    rollupOptions: {
      output: {
        entryFileNames: "playground.js",
        chunkFileNames: "playground-[name].js",
        assetFileNames: "playground.[ext]",
        inlineDynamicImports: true,
      },
    },
  },
  server: {
    // `npm run dev` talks to a running `cdcl serve`.
    proxy: { "/api": "http://127.0.0.1:8080" },
    fs: { allow: [".."] }, // the examples live in ../examples/smt
  },
});
