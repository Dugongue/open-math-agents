import Mathlib

/-!
# OEIS A100348: `n - 4^k` prime for all `k`

Source: https://oeis.org/A100348
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A100348 lists the `n` such that `n - 4^k` is prime for all `k > 0` with `4^k < n`. The largest
term appears to be `5833497`; the sequence is conjectured to be finite (cf. Erdős's A039669).

Conventions:
* `n ≥ 1`. (Numbers `n ≤ 4` satisfy the condition vacuously; finiteness is unaffected.)
-/

namespace OMA.S_oeis_a100348

/-- Only finitely many `n` have `n - 4^k` prime for every `k ≥ 1` with `4^k < n`. -/
theorem main : {n : ℕ | ∀ k : ℕ, 1 ≤ k → 4 ^ k < n → (n - 4 ^ k).Prime}.Finite := by
  sorry

end OMA.S_oeis_a100348
