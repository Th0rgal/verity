export default function Home() {
  return (
    <div style={{ padding: '2rem', maxWidth: '800px', margin: '0 auto' }}>
      <h1>Dumb Contracts</h1>
      <p><strong>Minimal Lean 4 EDSL for Smart Contracts with Formal Verification</strong></p>

      <blockquote>From runtime testing to mathematical proof</blockquote>

      <p>An 82-line core that handles realistic smart contracts, backed by machine-checked formal proofs of correctness.</p>

      <h2>Core Stats:</h2>
      <ul>
        <li>82 lines of Lean (minimal core)</li>
        <li>7 example contracts</li>
        <li>62 runtime tests (100% passing)</li>
        <li>11 formal proofs (100% verified)</li>
      </ul>

      <h2>Navigation</h2>
      <ul>
        <li><a href="https://github.com/Th0rgal/dumbcontracts">GitHub Repository</a></li>
        <li><a href="https://github.com/Th0rgal/dumbcontracts/blob/main/README.md">Full Documentation</a></li>
        <li><a href="https://github.com/Th0rgal/dumbcontracts/blob/main/VERIFICATION_ITERATION_1_SUMMARY.md">Verification Summary</a></li>
        <li><a href="https://github.com/Th0rgal/dumbcontracts/blob/main/RESEARCH.md">Research Log</a></li>
      </ul>

      <h2>The Value Proposition</h2>
      <p>Traditional smart contract testing gives you confidence through examples. Formal verification gives you certainty through proofs.</p>

      <p><strong>Result:</strong> Mathematical certainty for all possible inputs</p>

      <hr />

      <p><em>From runtime confidence to mathematical certainty</em></p>
    </div>
  )
}
