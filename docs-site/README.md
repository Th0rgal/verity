# Verity Documentation Site

Documentation website for Verity - built with [Next.js](https://nextjs.org) and [Nextra](https://nextra.site).

## Features

- 🤖 **AI-Friendly**: Auto-detects AI agents and serves markdown
- 📝 **Markdown/MDX**: All docs in markdown format
- 🔍 **Search**: Full-text search with Pagefind
- 🎨 **Dark Mode**: Built-in theme switching
- 📱 **Responsive**: Mobile-friendly design

## Development

```bash
# Install dependencies
npm install
# or
bun install

# Start dev server
npm run dev
# or
bun dev
```

Open [http://localhost:3003](http://localhost:3003)

## Build

```bash
npm run build
npm start
```

## Structure

```
docs-site/
├── app/
│   └── api/
│       └── docs/[...slug]/route.ts  # API for serving markdown
├── content/                          # Documentation pages (MDX)
│   ├── index.mdx                    # Homepage
│   ├── research.mdx                 # Research log
│   ├── iterations.mdx               # Iteration summaries
│   ├── examples.mdx                 # Example contracts
│   ├── core.mdx                     # Core architecture
│   └── _meta.js                     # Navigation config
├── public/
│   └── llms.txt                     # AI agent index
├── proxy.ts                         # Middleware for AI agent detection
└── next.config.mjs                  # Next.js config with Nextra
```

## AI Agent Support

The site automatically serves markdown to AI agents through:

1. **Auto-detection**: Known AI user agents get markdown automatically
2. **Explicit format**: Any page with `.md` extension or `?format=md` query
3. **Accept header**: Requests with `Accept: text/markdown`
4. **API routes**:
   - `/api/docs/_index` - List all documents (JSON)
   - `/api/docs/_all` - All docs concatenated (Markdown)
   - `/api/docs/[page]` - Single document (Markdown)

## Deployment

### Vercel (Recommended)

[![Deploy with Vercel](https://vercel.com/button)](https://vercel.com/new/clone?repository-url=https://github.com/lfglabs-dev/verity)

1. Connect your GitHub repository
2. Set build command: `npm run build`
3. Set output directory: `.next`
4. Deploy

#### Skip deployments for draft PRs

This project uses `vercel.json` with an `ignoreCommand`:

- `docs-site/scripts/vercel-ignore-draft-pr.sh`

Behavior:

- Draft PR: skips preview deployment
- Ready-for-review PR: runs deployment
- Non-PR deployment: runs deployment

Required environment variable in Vercel:

- `GITHUB_TOKEN` with `repo:read` access (for private repos) so the script can query PR draft status.

### Manual

```bash
npm run build
npm start
```

## License

MIT
