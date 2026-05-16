import { Layout, Navbar } from 'nextra-theme-docs'
import { Head } from 'nextra/components'
import { getPageMap } from 'nextra/page-map'
import 'nextra-theme-docs/style.css'
import './verity-code.css'

export const metadata = {
  title: {
    default: 'Verity',
    template: '%s – Verity',
  },
  description: 'Minimal Lean 4 EDSL for Smart Contracts with Formal Verification',
}

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
