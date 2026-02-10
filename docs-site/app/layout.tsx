import { Footer, Layout, Navbar } from 'nextra-theme-docs'
import { Banner, Head } from 'nextra/components'
import { getPageMap } from 'nextra/page-map'
import 'nextra-theme-docs/style.css'

export const metadata = {
  title: {
    default: 'Dumb Contracts',
    template: '%s – Dumb Contracts',
  },
  description: 'Minimal Lean 4 EDSL for Smart Contracts with Formal Verification',
}

const banner = (
  <Banner storageKey="verification-complete">
    82/82 theorems proven — 100% formal verification achieved
  </Banner>
)

const navbar = (
  <Navbar
    logo={<strong>Dumb Contracts</strong>}
    projectLink="https://github.com/Th0rgal/dumbcontracts"
  />
)

const footer = (
  <Footer>
    MIT {new Date().getFullYear()} ©{' '}
    <a href="https://github.com/Th0rgal" target="_blank" rel="noopener noreferrer">
      Th0rgal
    </a>
    . Built with{' '}
    <a href="https://nextra.site" target="_blank" rel="noopener noreferrer">
      Nextra
    </a>
    .
  </Footer>
)

export default async function RootLayout({ children }: { children: React.ReactNode }) {
  return (
    <html lang="en" dir="ltr" suppressHydrationWarning>
      <Head />
      <body>
        <Layout
          banner={banner}
          navbar={navbar}
          pageMap={await getPageMap()}
          docsRepositoryBase="https://github.com/Th0rgal/dumbcontracts/tree/main/docs-site"
          footer={footer}
          sidebar={{ defaultMenuCollapseLevel: 1 }}
          toc={{ backToTop: true }}
        >
          {children}
        </Layout>
      </body>
    </html>
  )
}
