import Mathlib

/-!
# OEIS A102483: powers of `2` without a zero in base `3`

Source: https://oeis.org/A102483
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A102483 lists the `k` such that `2^k` contains no zeros in base `3`: `0, 1, 2, 3, 4, 15`. The
author conjectured in 1973 that there are no further terms (still open); `main` states that these
are all.
-/

namespace OMA.S_oeis_a102483

/-- The only `k` with no digit `0` in the base-`3` expansion of `2^k` are `0, 1, 2, 3, 4, 15`. -/
theorem main : {k : ℕ | 0 ∉ Nat.digits 3 (2 ^ k)} = {0, 1, 2, 3, 4, 15} := by
  sorry

end OMA.S_oeis_a102483
