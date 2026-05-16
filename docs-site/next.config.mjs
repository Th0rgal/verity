import { dirname } from "path";
import { readFileSync } from "fs";
import { fileURLToPath } from "url";
import nextra from "nextra";
import { bundledLanguages, createHighlighter } from "shiki";

const configDir = dirname(fileURLToPath(import.meta.url));
const isDev = process.env.NODE_ENV !== "production";
const verityGrammar = JSON.parse(readFileSync(`${configDir}/syntaxes/verity.tmLanguage.json`, "utf8"));
const lfglabsCreamTheme = JSON.parse(readFileSync(`${configDir}/themes/lfglabs-cream.json`, "utf8"));

const withNextra = nextra({
  latex: true,
  search: {
    codeblocks: false,
  },
  mdxOptions: {
    rehypePrettyCodeOptions: {
      theme: lfglabsCreamTheme,
      getHighlighter(options) {
        const langs = Object.keys(bundledLanguages).filter((lang) => lang !== "mermaid");

        return createHighlighter({
          ...options,
          themes: [
            lfglabsCreamTheme,
            ...((options.themes ?? options.theme) ? [] : []),
          ],
          langs: [
            ...langs,
            {
              ...verityGrammar,
              name: "verity",
              aliases: ["vty"],
            },
          ],
        });
      },
    },
  },
});

export default withNextra({
  reactStrictMode: true,
  experimental: {
    optimizeCss: false,
  },
  ...(isDev ? { turbopack: { root: configDir } } : {}),
  images: {
    formats: ["image/avif", "image/webp"],
  },
});
