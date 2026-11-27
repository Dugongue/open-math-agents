import Mathlib

/-!
# OEIS A111151: numbers not of the form `a² + b³ + c⁴ + d⁵`

Source: https://oeis.org/A111151
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A111151 lists the numbers not of the form `a² + b³ + c⁴ + d⁵` with `a, b, c, d ≥ 0`:
`15, 23, 55, 62, 71, 471, 478, 510, 646, 806, 839, 879, 939, 1023, 1063, 1287, 2127, 5135, 6811,
7499, 9191, 26471`. It is conjectured that this list is complete.
-/

namespace OMA.S_oeis_a111151

/-- `n = a² + b³ + c⁴ + d⁵` for some naturals. -/
def Rep (n : ℕ) : Prop := ∃ a b c d : ℕ, n = a ^ 2 + b ^ 3 + c ^ 4 + d ^ 5

/-- The exceptions are exactly the listed numbers. -/
theorem main : {n : ℕ | ¬ Rep n} = {15, 23, 55, 62, 71, 471, 478, 510, 646, 806, 839, 879, 939,
    1023, 1063, 1287, 2127, 5135, 6811, 7499, 9191, 26471} := by
  sorry

end OMA.S_oeis_a111151
