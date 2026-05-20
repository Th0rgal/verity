import { generateStaticParamsFor, importPage } from 'nextra/pages'
import { useMDXComponents as getMDXComponents } from '../../mdx-components'

export const generateStaticParams = generateStaticParamsFor('mdxPath')

export async function generateMetadata(props: { params: Promise<{ mdxPath?: string[] }> }) {
  const params = await props.params
  const { metadata } = await importPage(params.mdxPath)
  const isHome = !params.mdxPath?.length
  const path = isHome ? '/' : `/${params.mdxPath!.join('/')}`
  const md: any = metadata ?? {}
  // On the home page, opt out of the "· Verity" title template so the
  // browser tab / SERP title stays clean. Override description with the
  // long-form site description for the homepage (which is more SEO-rich).
  const titleOverride = isHome
    ? {
        title: {
          absolute:
            'Verity, Formally Verified Smart Contract Compiler (Lean 4)',
        },
      }
    : {}
  return {
    ...md,
    ...titleOverride,
    alternates: {
      ...(md.alternates ?? {}),
      canonical: path,
    },
  }
}

const Wrapper = getMDXComponents().wrapper

export default async function Page(props: { params: Promise<{ mdxPath?: string[] }> }) {
  const params = await props.params
  const { default: MDXContent, toc, metadata, sourceCode } = await importPage(params.mdxPath)
  return (
    <Wrapper toc={toc} metadata={metadata} sourceCode={sourceCode}>
      <MDXContent {...props} params={params} />
    </Wrapper>
  )
}
