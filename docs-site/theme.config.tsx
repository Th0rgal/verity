const config = {
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
