import Mathlib

/-!
# OEIS A087659: Gosper's integrality conjecture

Source: https://oeis.org/A087659
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = ₃F₂(-n, (n+4)/2, (n+5)/2; 3, 2; -4)`. Conjecture (Gosper, 2004): the summands
`2 C(n, i) (n + 2i + 3)! / ((i+1)! (i+2)! (n+3)!)` are always integers.

Conventions:
* `n, i ≥ 0`; the quotient is taken in `ℚ` and asserted to be an integer.
-/

namespace OMA.S_oeis_a087659

/-- Gosper's summands are integers. -/
theorem main : ∀ n i : ℕ, ∃ z : ℤ,
    (2 * (n.choose i : ℚ) * (n + 2 * i + 3).factorial) /
      ((i + 1).factorial * (i + 2).factorial * (n + 3).factorial) = z := by
  sorry

end OMA.S_oeis_a087659
