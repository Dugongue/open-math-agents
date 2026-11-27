import Mathlib

/-!
# OEIS A085917: semiprimes `509203 · 2ⁿ - 1`

Source: https://oeis.org/A085917
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`509203` is the conjectured smallest Riesel number. The entry lists the first `n` with
`509203 · 2ⁿ - 1` a semiprime (`3, 4, 16, 34, 61, …`) and conjectures that there are infinitely
many semiprimes of this form.

Conventions:
* A semiprime has `Ω = 2` (two prime factors with multiplicity).
-/

namespace OMA.S_oeis_a085917

open ArithmeticFunction

/-- Infinitely many `n` make `509203 · 2ⁿ - 1` a semiprime. -/
theorem main : {n : ℕ | cardFactors (509203 * 2 ^ n - 1) = 2}.Infinite := by
  sorry

end OMA.S_oeis_a085917
