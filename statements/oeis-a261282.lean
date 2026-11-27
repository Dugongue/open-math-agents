import Mathlib

/-!
# OEIS A261282: `prime(k) prime(kn) = prime(p) + 2`

Source: https://oeis.org/A261282
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the least positive `k` such that `prime(k) prime(kn) = prime(p) + 2` for some prime `p`.
Conjecture (Sun): `a(n)` exists for every `n > 0`.

Conventions:
* `prime(i) = Nat.nth Nat.Prime (i - 1)`; `prime(p)` is the `p`-th prime with `p` itself prime.
-/

namespace OMA.S_oeis_a261282

/-- `prime(i)`. -/
noncomputable def P (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

/-- For every `n ≥ 1` some `k ≥ 1` and prime `p` satisfy `prime(k) prime(kn) = prime(p) + 2`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k p : ℕ, 1 ≤ k ∧ p.Prime ∧ P k * P (k * n) = P p + 2 := by
  sorry

end OMA.S_oeis_a261282
