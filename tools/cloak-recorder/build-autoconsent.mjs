import { build } from "esbuild";
import { fileURLToPath } from "node:url";
import path from "node:path";

const here = path.dirname(fileURLToPath(import.meta.url));

await build({
  entryPoints: [path.join(here, "autoconsent-entry.js")],
  outfile: path.join(here, "autoconsent.inject.js"),
  bundle: true,
  format: "iife",
  platform: "browser",
  target: ["chrome146"],
  minify: false,
  sourcemap: false,
  legalComments: "none",
});

console.log("built autoconsent.inject.js");
