import { Layout, Navbar } from 'nextra-theme-docs'
import { Head } from 'nextra/components'
import { getPageMap } from 'nextra/page-map'
import 'nextra-theme-docs/style.css'
import './verity-site.css'
import './verity-code.css'

const SITE_URL = 'https://veritylang.com'
const SITE_TITLE = 'Verity, Formally Verified Smart Contract Compiler (Lean 4)'
const SITE_DESCRIPTION =
  'Verity is a formally verified smart contract compiler for Ethereum, written in Lean 4. Write the spec, write the implementation, and prove they agree. Every claim is machine-checked at compile time, and the compiler itself is proven to preserve semantics from EDSL to EVM bytecode.'
const SITE_KEYWORDS = [
  'Verity',
  'Verity Lang',
  'veritylang',
  'formal verification',
  'smart contract verification',
  'verified compiler',
  'Lean 4',
  'Ethereum',
  'EVM',
  'Solidity alternative',
  'theorem proving',
  'EDSL',
  'LFG Labs',
]

export const metadata = {
  metadataBase: new URL(SITE_URL),
  title: {
    default: SITE_TITLE,
    template: '%s · Verity',
  },
  description: SITE_DESCRIPTION,
  keywords: SITE_KEYWORDS,
  applicationName: 'Verity',
  authors: [{ name: 'LFG Labs', url: 'https://lfglabs.dev' }],
  creator: 'LFG Labs',
  publisher: 'LFG Labs',
  category: 'technology',
  icons: {
    icon: '/verity.svg',
    shortcut: '/verity.svg',
    apple: '/verity.svg',
  },
  openGraph: {
    type: 'website',
    siteName: 'Verity',
    title: SITE_TITLE,
    description: SITE_DESCRIPTION,
    url: SITE_URL,
    locale: 'en_US',
    images: [
      {
        url: '/og.png',
        width: 1200,
        height: 630,
        alt: 'Verity, Formally Verified Smart Contract Compiler (Lean 4)',
      },
    ],
  },
  twitter: {
    card: 'summary_large_image',
    title: SITE_TITLE,
    description: SITE_DESCRIPTION,
    images: ['/og.png'],
    site: '@lfglabsdev',
    creator: '@lfglabsdev',
  },
  robots: {
    index: true,
    follow: true,
    googleBot: {
      index: true,
      follow: true,
      'max-snippet': -1,
      'max-image-preview': 'large',
      'max-video-preview': -1,
    },
  },
}

const structuredData = {
  '@context': 'https://schema.org',
  '@graph': [
    {
      '@type': 'SoftwareApplication',
      name: 'Verity',
      applicationCategory: 'DeveloperApplication',
      operatingSystem: 'Cross-platform',
      url: SITE_URL,
      description: SITE_DESCRIPTION,
      programmingLanguage: 'Lean 4',
      license: 'https://github.com/lfglabs-dev/verity/blob/main/LICENSE.md',
      codeRepository: 'https://github.com/lfglabs-dev/verity',
      offers: { '@type': 'Offer', price: '0', priceCurrency: 'USD' },
      author: {
        '@type': 'Organization',
        name: 'LFG Labs',
        url: 'https://lfglabs.dev',
      },
    },
    {
      '@type': 'Organization',
      name: 'LFG Labs',
      url: 'https://lfglabs.dev',
      sameAs: [
        'https://github.com/lfglabs-dev',
        'https://lfglabs.dev',
      ],
    },
  ],
}

const navbar = (
  <Navbar
    logo={
      <span className="verity-brand">
        <img src="/verity.svg" alt="" width="22" height="22" />
        <strong>Verity</strong>
      </span>
    }
    projectLink="https://github.com/lfglabs-dev/verity"
  />
)

export default async function RootLayout({ children }: { children: React.ReactNode }) {
  return (
    <html lang="en" dir="ltr" suppressHydrationWarning>
      <Head />
      <body>
        <Layout
          navbar={navbar}
          pageMap={await getPageMap()}
          docsRepositoryBase="https://github.com/lfglabs-dev/verity/tree/main/docs-site"
          sidebar={{ defaultMenuCollapseLevel: 1 }}
          toc={{ backToTop: true }}
          footer={
            <footer className="verity-footer">
              <p>
                Verity is a research project by{' '}
                <a href="https://lfglabs.dev" target="_blank" rel="noopener">
                  LFG Labs
                </a>
                . Read the{' '}
                <a href="https://lfglabs.dev/papers/verity.pdf" target="_blank" rel="noopener">
                  paper
                </a>
                {' · '}
                <a href="https://github.com/lfglabs-dev/verity" target="_blank" rel="noopener">
                  GitHub
                </a>
                {' · '}
                <a href="https://github.com/lfglabs-dev/verity-benchmark" target="_blank" rel="noopener">
                  Benchmark
                </a>
                .
              </p>
            </footer>
          }
        >
          {children}
        </Layout>
        <script
          type="application/ld+json"
          dangerouslySetInnerHTML={{ __html: JSON.stringify(structuredData) }}
        />
      </body>
    </html>
  )
}
