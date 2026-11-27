import Mathlib

/-!
# OEIS A079047: primes between `p` and `p²`

Source: https://oeis.org/A079047
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of primes strictly between `prime(n)` and `prime(n)²`. Conjecture (OEIS
entry): `25` and `64` are the only terms that are perfect squares.

Conventions:
* `prime(n) = Nat.nth Nat.Prime (n - 1)`, `n ≥ 1`. `main` states that the set of square values of
  `a` is `{25, 64}`.
-/

namespace OMA.S_oeis_a079047

/-- `a(n)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  let p := Nat.nth Nat.Prime (n - 1)
  ((Finset.Ioo p (p ^ 2)).filter Nat.Prime).card

/-- The square values of `a` are exactly `25` and `64`. -/
theorem main : {m : ℕ | IsSquare m ∧ ∃ n, 1 ≤ n ∧ a n = m} = {25, 64} := by
  sorry

end OMA.S_oeis_a079047
