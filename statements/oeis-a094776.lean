import Mathlib

/-!
# A094776: a(n) = largest k such that the decimal representation of 2^k does not contain the digit n.

Source: https://oeis.org/A094776
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

a(0) = 86 because 2^86 = 77371252455336267181195264 is conjectured to be the
highest power of 2 that doesn't contain the digit 0.
-/

namespace OMA.S_oeis_a094776

theorem main :
    ∀ k : ℕ, 86 < k → 0 ∈ Nat.digits 10 (2 ^ k) := by
  sorry

end OMA.S_oeis_a094776
