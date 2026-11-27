import Mathlib

/-!
# OEIS A056777: `φ(k+12) = φ(k)+12` and `σ(k+12) = σ(k)+12`

Source: https://oeis.org/A056777
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A056777 lists the composite `k` with `φ(k + 12) = φ(k) + 12` and `σ(k + 12) = σ(k) + 12`. If
`p, p+2, p+6, p+8` are all prime then `k = p(p+8)` is a term (`k + 12 = (p+2)(p+6)`). Conjecture
(OEIS entry): all terms are of this form.
-/

namespace OMA.S_oeis_a056777

open ArithmeticFunction

/-- Every term is `p(p+8)` for a prime quadruple `p, p+2, p+6, p+8`. -/
theorem main : ∀ k : ℕ, 1 < k → ¬ k.Prime →
    Nat.totient (k + 12) = Nat.totient k + 12 → ArithmeticFunction.sigma 1 (k + 12) = ArithmeticFunction.sigma 1 k + 12 →
    ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime ∧ k = p * (p + 8) := by
  sorry

end OMA.S_oeis_a056777
