import { importPage } from 'nextra/pages'
import { useMDXComponents } from 'nextra/mdx-components'
import { MDXProvider } from '@mdx-js/react'

export async function generateMetadata(props) {
  const params = await props.params
  const { metadata } = await importPage(params.mdxPath)
  return {
    title: metadata.title,
    description: metadata.description,
  }
}

export default async function Page(props) {
  const params = await props.params
  const result = await importPage(params.mdxPath)

  const { default: MDXContent } = result
  const components = useMDXComponents()

  return (
    <MDXProvider components={components}>
      <MDXContent />
    </MDXProvider>
  )
}
