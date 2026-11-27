import Mathlib

/-!
# OEIS A087412: solutions of `x³ + y³ ≡ 1 (mod n)`

Source: https://oeis.org/A087412
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of solutions of `x³ + y³ ≡ 1 (mod n)`. Conjecture (Howroyd, 2018):
`a(3^e) = 2 · 3^e` for `e > 1`, and `a(p^e) = p^(e-1) (p - 1 + ∑_{b=1}^{p-1} (12 b⁻¹ - 3b² | p))`
for primes `p ≠ 3` (`( · | p)` the Legendre symbol, `b⁻¹` the inverse mod `p`).

Conventions:
* Solutions are pairs in `ZMod n`; `e ≥ 1` in the second formula. The Legendre symbol is
  `legendreSym p` applied to the integer representative (`ZMod.val`) of `12 b⁻¹ - 3b² ∈ ZMod p`.
-/

namespace OMA.S_oeis_a087412

/-- `a(n)`. -/
noncomputable def a (n : ℕ) : ℕ := {v : ZMod n × ZMod n | v.1 ^ 3 + v.2 ^ 3 = 1}.ncard

/-- Both parts of the conjecture. -/
theorem main :
    (∀ e : ℕ, 1 < e → a (3 ^ e) = 2 * 3 ^ e) ∧
    (∀ (p : ℕ) [Fact p.Prime], p ≠ 3 → ∀ e : ℕ, 1 ≤ e →
      (a (p ^ e) : ℤ) = (p : ℤ) ^ (e - 1) * ((p : ℤ) - 1 + ∑ b ∈ Finset.Icc 1 (p - 1),
        legendreSym p ((12 * (b : ZMod p)⁻¹ - 3 * (b : ZMod p) ^ 2).val : ℤ))) := by
  sorry

end OMA.S_oeis_a087412
