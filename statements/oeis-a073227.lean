import Mathlib

/-!
# OEIS A073227: transcendence of `e^(e^e)`

Source: https://oeis.org/A073227
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A073227 is the decimal expansion of `e^(e^e)`. The entry notes that a weak form of Schanuel's
conjecture implies that `e^(e^e)` is transcendental (Marques–Sondow 2012); `main` states that it
is transcendental.
-/

namespace OMA.S_oeis_a073227

/-- `e^(e^e)` is transcendental. -/
theorem main : Transcendental ℚ (Real.exp (Real.exp (Real.exp 1))) := by
  sorry

end OMA.S_oeis_a073227
