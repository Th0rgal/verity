import type { MetadataRoute } from 'next'

const ROUTES = [
  '',
  // Introduction
  '/architecture',
  '/trust-model',
  // Tutorials
  '/getting-started',
  '/first-contract',
  // How-To Guides
  '/guides/add-contract',
  '/guides/solidity-to-verity',
  '/guides/production-solidity-patterns',
  '/guides/linking-libraries',
  '/guides/debugging-proofs',
  // Reference
  '/examples',
  '/core',
  '/edsl-api-reference',
  '/compiler',
  '/verification',
  '/glossary',
  // Explanation
  '/compiler-architecture',
  '/proof-techniques',
  '/research',
  '/research/iterations',
  '/faq',
  // Project
  '/syntax-highlighting',
]

export default function sitemap(): MetadataRoute.Sitemap {
  const base = 'https://veritylang.com'
  const lastModified = new Date()
  return ROUTES.map((path) => ({
    url: `${base}${path}`,
    lastModified,
    changeFrequency: path === '' ? 'weekly' : 'monthly',
    priority: path === '' ? 1.0 : 0.7,
  }))
}
