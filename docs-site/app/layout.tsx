import { Layout, Navbar } from 'nextra-theme-docs'
import { Banner, Head } from 'nextra/components'
import { getPageMap } from 'nextra/page-map'
import 'nextra-theme-docs/style.css'

export const metadata = {
  title: {
    default: 'Verity',
    template: '%s – Verity',
  },
  description: 'Minimal Lean 4 EDSL for Smart Contracts with Formal Verification',
}

const banner = (
  <Banner storageKey="verification-complete">
    412/412 theorems proven — 100% formal verification
  </Banner>
)

const navbar = (
  <Navbar
    logo={<strong>Verity</strong>}
    projectLink="https://github.com/Th0rgal/verity"
  />
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
          docsRepositoryBase="https://github.com/Th0rgal/verity/tree/main/docs-site"
          sidebar={{ defaultMenuCollapseLevel: 1 }}
          toc={{ backToTop: true }}
        >
          {children}
        </Layout>
      </body>
    </html>
  )
}
