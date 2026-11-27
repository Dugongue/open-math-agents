import Mathlib

/-!
# OEIS A136958: `k` and `k²` with digits in `{0, 4, 7, 8}`

Source: https://oeis.org/A136958
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A136958 lists the `k` such that `k` and `k²` use only the digits `0, 4, 7, 8`. Conjectures (OEIS
entry): (1) the digit `4` never appears in the terms; (2) all nonzero terms are of the form
`88 · 10^m` or `878 · 10^m`. (2) implies (1); `main` states (2).
-/

namespace OMA.S_oeis_a136958

/-- All decimal digits of `m` lie in `{0, 4, 7, 8}`. -/
def Good (m : ℕ) : Prop := ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 4 ∨ d = 7 ∨ d = 8

/-- Every nonzero term is `88 · 10^m` or `878 · 10^m`. -/
theorem main : ∀ k : ℕ, 1 ≤ k → Good k → Good (k ^ 2) →
    ∃ m : ℕ, k = 88 * 10 ^ m ∨ k = 878 * 10 ^ m := by
  sorry

end OMA.S_oeis_a136958
