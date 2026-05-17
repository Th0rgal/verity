const primaryLink = { href: '/guides/first-contract', label: 'Start with a contract' }

const secondaryLinks = [
  { href: '/compiler', label: 'Compiler model' },
  { href: '/verification', label: 'Verification status' },
  { href: '/research', label: 'Research notes' },
]

const brief = [
  { label: 'Pipeline', value: <>Spec&nbsp;→ EDSL&nbsp;→ IR&nbsp;→ Yul</> },
  { label: 'Surface', value: 'Storage, guards, events, typed externals' },
  { label: 'Assurance', value: 'Machine-checked claims, explicit assumptions' },
]

export function VerityHero() {
  return (
    <section className="verity-hero" aria-labelledby="verity-hero-title">
      <header className="verity-hero__head">
        <p className="verity-kicker">Lean-native verification language</p>
        <h1 id="verity-hero-title">
          Verity<span aria-hidden="true" className="verity-hero__terminal">.</span>
        </h1>
        <p className="verity-hero__dek">
          Write smart contracts in Lean. Compile to EVM.{' '}
          <em>Prove&nbsp;them correct</em>.
        </p>
      </header>

      <div className="verity-hero__body">
        <div className="verity-hero__copy">
          <nav className="verity-hero__links" aria-label="Primary documentation links">
            <a className="verity-hero__cta" href={primaryLink.href}>
              {primaryLink.label}
              <span aria-hidden="true">→</span>
            </a>
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
        </div>

        <aside className="verity-hero__brief" aria-label="Verification brief">
          <p className="verity-hero__brief-label">At a glance</p>
          <dl>
            {brief.map((item) => (
              <div key={item.label}>
                <dt>{item.label}</dt>
                <dd>{item.value}</dd>
              </div>
            ))}
          </dl>
        </aside>
      </div>
    </section>
  )
}
