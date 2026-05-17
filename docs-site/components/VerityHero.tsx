const claims = [
  'Lean proofs live next to executable contract code.',
  'Compiler models preserve typed storage, guards, and ABI surfaces.',
  'Generated EVM artifacts carry explicit proof and trust boundaries.',
]

const links = [
  { href: '/guides/first-contract', label: 'Start with a contract' },
  { href: '/compiler', label: 'Read the compiler model' },
  { href: '/verification', label: 'View verification status' },
]

export function VerityHero() {
  return (
    <section className="verity-hero" aria-labelledby="verity-hero-title">
      <div className="verity-hero__copy">
        <p className="verity-kicker">Lean-native verification language</p>
        <h1 id="verity-hero-title">Verity</h1>
        <p className="verity-hero__dek">A Lean-native language for verified smart contracts.</p>
        <ul className="verity-claim-list" aria-label="Verification claims">
          {claims.map((claim) => (
            <li key={claim}>{claim}</li>
          ))}
        </ul>
        <nav className="verity-hero__links" aria-label="Primary documentation links">
          {links.map((link) => (
            <a key={link.href} href={link.href}>
              {link.label}
            </a>
          ))}
        </nav>
      </div>
      <aside className="verity-hero__brief" aria-label="Verification brief">
        <div>
          <span>Proof surface</span>
          <strong>Spec&nbsp;→ EDSL&nbsp;→ IR&nbsp;→ Yul</strong>
        </div>
        <div>
          <span>Contract shape</span>
          <strong>Storage, guards, events, typed externals</strong>
        </div>
        <div>
          <span>Audit posture</span>
          <strong>Machine-checked claims plus explicit assumptions</strong>
        </div>
      </aside>
    </section>
  )
}
