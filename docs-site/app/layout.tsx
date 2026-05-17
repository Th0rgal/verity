import { Layout, Navbar } from 'nextra-theme-docs'
import { Head } from 'nextra/components'
import { getPageMap } from 'nextra/page-map'
import 'nextra-theme-docs/style.css'
import './verity-site.css'
import './verity-code.css'

export const metadata = {
  title: {
    default: 'Verity',
    template: '%s',
  },
  description: 'Minimal Lean 4 EDSL for Smart Contracts with Formal Verification',
  icons: {
    icon: '/verity.svg',
    shortcut: '/verity.svg',
    apple: '/verity.svg',
  },
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
        >
          {children}
        </Layout>
      </body>
    </html>
  )
}
