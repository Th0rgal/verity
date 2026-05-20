// Generate /public/og.png (1200x630) and /public/og-square.png (1200x1200)
// for OpenGraph / Twitter previews. Uses rsvg-convert (librsvg) for the logo
// glyph, then composites a dark themed banner via a synthesized SVG.
//
// Run: node scripts/generate-og.mjs
import { execSync } from 'node:child_process'
import { writeFileSync, mkdirSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'

const SITE = 'veritylang.com'
const HEADLINE = 'Formally verified smart contracts.'
const SUBLINE = 'Write the spec. Write the implementation. Prove they agree.'
const TAGS = 'Lean 4  ·  Ethereum  ·  EVM  ·  by LFG Labs'

function bannerSvg({ width, height, headlineSize, sublineSize, logoSize, logoY, textX, headlineY }) {
  return `<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}" viewBox="0 0 ${width} ${height}">
  <defs>
    <linearGradient id="bg" x1="0" y1="0" x2="1" y2="1">
      <stop offset="0%" stop-color="#0b1416"/>
      <stop offset="100%" stop-color="#04282b"/>
    </linearGradient>
    <radialGradient id="glow" cx="22%" cy="38%" r="55%">
      <stop offset="0%" stop-color="#0a7d7d" stop-opacity="0.35"/>
      <stop offset="100%" stop-color="#0a7d7d" stop-opacity="0"/>
    </radialGradient>
  </defs>
  <rect width="${width}" height="${height}" fill="url(#bg)"/>
  <rect width="${width}" height="${height}" fill="url(#glow)"/>
  <!-- Verity glyph (replicated from /public/verity.svg) -->
  <g transform="translate(80, ${logoY}) scale(${logoSize / 507})" shape-rendering="crispEdges">
    <polygon points="0,0 169,0 84.5,147" fill="#cfd8d8"/>
    <polygon points="169,0 84.5,147 253.5,147" fill="#9aa5a5"/>
    <polygon points="338,0 507,0 422.5,147" fill="#b9c1c1"/>
    <polygon points="338,0 422.5,147 253.5,147" fill="#a8b1b1"/>
    <polygon points="84.5,147 253.5,147 169,294" fill="#5b6464"/>
    <polygon points="253.5,147 422.5,147 338,294" fill="#8a9494"/>
    <polygon points="253.5,147 169,294 338,294" fill="#707979"/>
    <polygon points="169,294 338,294 253.5,441" fill="#3e4646"/>
  </g>
  <text x="${textX}" y="${headlineY}" font-family="Helvetica, Arial, sans-serif" font-weight="700" font-size="${headlineSize}" fill="#f1f5f5" letter-spacing="-1">Verity</text>
  <text x="${textX}" y="${headlineY + Math.round(headlineSize * 0.95)}" font-family="Helvetica, Arial, sans-serif" font-weight="600" font-size="${Math.round(headlineSize * 0.45)}" fill="#e6f0ee">${HEADLINE}</text>
  <text x="${textX}" y="${headlineY + Math.round(headlineSize * 0.95) + Math.round(headlineSize * 0.55)}" font-family="Helvetica, Arial, sans-serif" font-weight="400" font-size="${sublineSize}" fill="#9ab8b6">${SUBLINE}</text>
  <text x="${textX}" y="${height - 70}" font-family="Helvetica, Arial, sans-serif" font-weight="500" font-size="26" fill="#5e8e8c" letter-spacing="1">${TAGS}</text>
  <text x="${width - 80}" y="${height - 70}" text-anchor="end" font-family="Helvetica, Arial, sans-serif" font-weight="500" font-size="26" fill="#5e8e8c">${SITE}</text>
</svg>`
}

function build(outPath, opts) {
  const svgPath = join(tmpdir(), `og-${Date.now()}-${opts.width}.svg`)
  writeFileSync(svgPath, bannerSvg(opts))
  execSync(`rsvg-convert -w ${opts.width} -h ${opts.height} "${svgPath}" -o "${outPath}"`)
  console.log(`wrote ${outPath} (${opts.width}x${opts.height})`)
}

const pub = new URL('../public/', import.meta.url).pathname
mkdirSync(pub, { recursive: true })

build(join(pub, 'og.png'), {
  width: 1200,
  height: 630,
  headlineSize: 96,
  sublineSize: 28,
  logoSize: 220,
  logoY: 170,
  textX: 340,
  headlineY: 250,
})

build(join(pub, 'og-square.png'), {
  width: 1200,
  height: 1200,
  headlineSize: 120,
  sublineSize: 34,
  logoSize: 320,
  logoY: 200,
  textX: 460,
  headlineY: 340,
})
