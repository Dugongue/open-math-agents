import Mathlib

/-!
# A008839: Numbers k such that the decimal expansion of 5^k contains no zeros

Source: https://oeis.org/A008839
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture:
`5^58` is the largest power of `5` whose base-10 expansion contains no `0` digit;
equivalently, for every integer `k > 58`, the decimal expansion of `5^k` contains the digit `0`.

Conventions:
- Base-10 digits of a positive natural number `m` are given by `Nat.digits 10 m`.
-/

namespace OMA.S_oeis_a008839

theorem main : ∀ k : ℕ, k > 58 → 0 ∈ Nat.digits 10 (5 ^ k) := by
  sorry

end OMA.S_oeis_a008839
