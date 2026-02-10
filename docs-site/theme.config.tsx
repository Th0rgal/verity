import { useConfig, type DocsThemeConfig } from "nextra-theme-docs";

const config: DocsThemeConfig = {
  logo: <strong>Dumb Contracts</strong>,
  project: {
    link: "https://github.com/Th0rgal/dumbcontracts",
  },
  docsRepositoryBase: "https://github.com/Th0rgal/dumbcontracts/tree/main/docs-site",
  footer: {
    content: (
      <span>
        MIT {new Date().getFullYear()} ©{" "}
        <a href="https://github.com/Th0rgal" target="_blank" rel="noopener noreferrer">
          Th0rgal
        </a>
        . Built with{" "}
        <a href="https://nextra.site" target="_blank" rel="noopener noreferrer">
          Nextra
        </a>
        .
      </span>
    ),
  },
  head: () => {
    const config = useConfig();
    const title = config.title ? `${config.title} – Dumb Contracts` : "Dumb Contracts";
    const description =
      config.frontMatter.description || "Minimal Lean EDSL for Smart Contracts";

    return (
      <>
        <title>{title}</title>
        <meta name="description" content={description} />
        <meta name="og:title" content={title} />
        <meta name="og:description" content={description} />
        <meta name="viewport" content="width=device-width, initial-scale=1.0" />
        <link rel="icon" href="/favicon.ico" />
      </>
    );
  },
  useNextSeoProps() {
    return {
      titleTemplate: "%s – Dumb Contracts",
    };
  },
  banner: {
    key: "ai-friendly",
    content: (
      <div>
        🤖 AI-friendly docs: Request any page as <code>.md</code> or check{" "}
        <a href="/llms.txt" target="_blank" rel="noopener noreferrer">
          /llms.txt
        </a>
      </div>
    ),
  },
  sidebar: {
    defaultMenuCollapseLevel: 1,
  },
  toc: {
    backToTop: true,
  },
};

export default config;
