import type { Metadata } from 'next'

export const metadata: Metadata = {
  title: {
    default: 'Dumb Contracts',
    template: '%s – Dumb Contracts',
  },
  description: 'Minimal Lean 4 EDSL for Smart Contracts with Formal Verification',
  icons: {
    icon: '/favicon.ico',
  },
  openGraph: {
    title: 'Dumb Contracts',
    description: 'Minimal Lean 4 EDSL for Smart Contracts with Formal Verification',
  },
}

export default function RootLayout({ children }: { children: React.ReactNode }) {
  return children;
}
