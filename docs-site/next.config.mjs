import { dirname } from "path";
import { readFileSync } from "fs";
import { fileURLToPath } from "url";
import nextra from "nextra";
import { bundledLanguages, createHighlighter } from "shiki";

const configDir = dirname(fileURLToPath(import.meta.url));
const isDev = process.env.NODE_ENV !== "production";
const verityGrammar = JSON.parse(readFileSync(`${configDir}/syntaxes/verity.tmLanguage.json`, "utf8"));
const lfglabsCreamTheme = JSON.parse(readFileSync(`${configDir}/themes/lfglabs-cream.json`, "utf8"));
const verityDarkTheme = JSON.parse(readFileSync(`${configDir}/themes/verity-dark.json`, "utf8"));

const withNextra = nextra({
  latex: true,
  search: {
    codeblocks: false,
  },
  mdxOptions: {
    rehypePrettyCodeOptions: {
      theme: {
        light: lfglabsCreamTheme,
        dark: verityDarkTheme,
      },
      getHighlighter(options) {
        const langs = Object.keys(bundledLanguages).filter((lang) => lang !== "mermaid");

        return createHighlighter({
          ...options,
          themes: [
            lfglabsCreamTheme,
            verityDarkTheme,
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
  // Redirect legacy URLs to the new IA so old bookmarks / external
  // links don't 404 after the restructure.
  async redirects() {
    return [
      // Tutorial moved from /guides/ to top-level.
      { source: "/guides/first-contract", destination: "/first-contract", permanent: true },
      // The "Add a Contract" page moved into /guides/.
      { source: "/add-contract", destination: "/guides/add-contract", permanent: true },
      // Syntax-highlighting page moved out of /guides/ to top-level.
      { source: "/guides/verity-syntax-highlighting", destination: "/syntax-highlighting", permanent: true },
    ];
  },
});
