const primaryLink = { href: '/first-contract', label: 'Start with a contract' }

const paperLink = {
  href: 'https://lfglabs.dev/papers/verity.pdf',
  label: 'Read the paper',
}

const secondaryLinks = [
  { href: '/compiler', label: 'Compiler model' },
  { href: '/verification', label: 'Verification status' },
  { href: '/faq', label: 'FAQ' },
]

const facts = [
  { label: 'Pipeline', value: <>Spec&nbsp;→ EDSL&nbsp;→ IR&nbsp;→ Yul</> },
  { label: 'Surface', value: 'Storage, guards, events, typed externals' },
  { label: 'Assurance', value: 'Machine-checked claims, explicit assumptions' },
]

export function VerityHero() {
  return (
    <section className="verity-hero" aria-labelledby="verity-hero-title">
      <header className="verity-hero__head">
        <p className="verity-kicker">
          Lean&nbsp;4 <span aria-hidden="true">·</span> Formal verification <span aria-hidden="true">·</span> EVM
        </p>
        <h1 id="verity-hero-title">
          Verity<span aria-hidden="true" className="verity-hero__terminal">.</span>
        </h1>
        <p className="verity-hero__dek">
          Write smart contracts in Lean. Compile to EVM.{' '}
          <em>Prove&nbsp;them correct</em>.
        </p>

        <nav className="verity-hero__links" aria-label="Primary documentation links">
          <div className="verity-hero__cta-row">
            <a className="verity-hero__cta" href={primaryLink.href}>
              {primaryLink.label}
              <span aria-hidden="true">→</span>
            </a>
            <a
              className="verity-hero__paper"
              href={paperLink.href}
              target="_blank"
              rel="noopener noreferrer"
            >
              <svg
                aria-hidden="true"
                viewBox="0 0 16 20"
                width="14"
                height="14"
                fill="none"
                stroke="currentColor"
                strokeWidth="1.6"
                strokeLinecap="round"
                strokeLinejoin="round"
              >
                <path d="M2 1.5h7l5 5v12a1 1 0 0 1-1 1H2a1 1 0 0 1-1-1V2.5a1 1 0 0 1 1-1Z" />
                <path d="M9 1.5V6.5h5" />
                <path d="M4 11h8M4 14h8M4 8h3" />
              </svg>
              {paperLink.label}
              <span aria-hidden="true" className="verity-hero__paper-arrow">↗</span>
            </a>
          </div>
          <ul className="verity-hero__more">
            {secondaryLinks.map((link) => (
              <li key={link.href}>
                <a href={link.href}>
                  {link.label}
                  <span aria-hidden="true">↗</span>
                </a>
              </li>
            ))}
          </ul>
        </nav>
      </header>

      <dl className="verity-hero__facts" aria-label="At a glance">
        {facts.map((item) => (
          <div key={item.label}>
            <dt>{item.label}</dt>
            <dd>{item.value}</dd>
          </div>
        ))}
      </dl>
    </section>
  )
}
