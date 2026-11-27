import Mathlib

/-!
# OEIS A094787: smallest prime `p` with `p + n` a perfect power

Source: https://oeis.org/A094787
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the smallest prime `p` such that `p + n` is a perfect power `m^k`, `k ≥ 2`. Conjecture
(OEIS entry): every prime occurs in this sequence.

Conventions:
* `n ≥ 1`; perfect powers are `m^k` with `m ≥ 1`, `k ≥ 2`; `a(n)` is `sInf` of the admissible
  primes.
-/

namespace OMA.S_oeis_a094787

/-- `x` is a perfect power. -/
def IsPerfectPower (x : ℕ) : Prop := ∃ m k : ℕ, 1 ≤ m ∧ 2 ≤ k ∧ x = m ^ k

/-- `a(n)`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {p : ℕ | p.Prime ∧ IsPerfectPower (p + n)}

/-- Every prime is some `a(n)`. -/
theorem main : ∀ q : ℕ, q.Prime → ∃ n : ℕ, 1 ≤ n ∧ a n = q := by
  sorry

end OMA.S_oeis_a094787
