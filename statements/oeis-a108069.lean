import Mathlib

/-!
# OEIS A108069: representations `n = i! j!`

Source: https://oeis.org/A108069
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of ordered pairs `(i, j)`, `i, j ≥ 1`, with `i! j! = n`. Conjecture (Kane):
`max_{n → ∞} a(n) = 4`.

Conventions:
* Read as `limsup a(n) = 4`: eventually `a(n) ≤ 4`, and `a(n) = 4` for infinitely many `n`.
  For `n ≥ 1` only `i, j ≤ n` can occur, so `a(n)` is a finite count.
-/

namespace OMA.S_oeis_a108069

open Filter

/-- `a(n)`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun ij => ij.1.factorial * ij.2.factorial = n).card

/-- `limsup a(n) = 4`. -/
theorem main : (∀ᶠ n in atTop, a n ≤ 4) ∧ (∃ᶠ n in atTop, a n = 4) := by
  sorry

end OMA.S_oeis_a108069
