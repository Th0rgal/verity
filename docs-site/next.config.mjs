import { dirname } from "path";
import { fileURLToPath } from "url";
import nextra from "nextra";

const configDir = dirname(fileURLToPath(import.meta.url));
const isDev = process.env.NODE_ENV !== "production";

const withNextra = nextra({
  latex: true,
  search: {
    codeblocks: false,
  },
  contentDirBasePath: "/",
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
