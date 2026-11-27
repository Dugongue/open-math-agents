import Mathlib

/-!
# OEIS A085398: least `k > 1` with `Φₙ(k)` prime

Source: https://oeis.org/A085398
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the least `k > 1` such that the cyclotomic value `Φₙ(k)` is prime. Conjecture (OEIS
entry; implied by Bunyakovsky's conjecture): `a(n)` is defined for all `n`.

Conventions:
* `n ≥ 1`; `Φₙ` is Mathlib's `Polynomial.cyclotomic n ℤ`, and `Φₙ(k)` prime means its value is a
  prime integer (`Prime` in `ℤ`).
-/

namespace OMA.S_oeis_a085398

/-- For every `n ≥ 1` some `k > 1` makes `Φₙ(k)` prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℤ, 1 < k ∧ Prime ((Polynomial.cyclotomic n ℤ).eval k) := by
  sorry

end OMA.S_oeis_a085398
