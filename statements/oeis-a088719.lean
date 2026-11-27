import Mathlib

/-!
# OEIS A088719: sums of two seventh powers

Source: https://oeis.org/A088719
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A088719 lists the numbers `a⁷ + b⁷` with `0 < a < b` that have exactly one such representation.
Conjecture (OEIS entry): no number can be expressed as such a sum in more than one way.
-/

namespace OMA.S_oeis_a088719

/-- `a⁷ + b⁷` with `0 < a < b` determines `(a, b)`. -/
theorem main : ∀ a b c d : ℕ, 0 < a → a < b → 0 < c → c < d →
    a ^ 7 + b ^ 7 = c ^ 7 + d ^ 7 → a = c ∧ b = d := by
  sorry

end OMA.S_oeis_a088719
