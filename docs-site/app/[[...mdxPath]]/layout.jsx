import { getPageMap } from 'nextra/page-map'
import { Layout } from 'nextra-theme-docs'

import themeConfig from '../../theme.config'

export default async function MDXLayout({ children }) {
  const pageMap = await getPageMap()

  return (
    <Layout {...themeConfig} pageMap={pageMap}>
      {children}
    </Layout>
  )
}
