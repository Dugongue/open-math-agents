import Mathlib

/-!
# OEIS A111364: every value occurs among the zero counts A033093

Source: https://oeis.org/A111364
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A111364 gives the index of the first occurrence of `n` in A033093 (the total number of `0` digits
of `m` written in all bases `2 ≤ b ≤ m + 1`), or `0` if absent. Conjecture (OEIS entry): the
sequence contains no zeros, i.e. A033093 takes every nonnegative integer value.
-/

namespace OMA.S_oeis_a111364

/-- A033093: total number of zero digits of `m` in bases `2, …, m + 1`. -/
def z (m : ℕ) : ℕ :=
  ∑ b ∈ Finset.Icc 2 (m + 1), ((Nat.digits b m).filter (· = 0)).length

/-- Every `n` is a value of A033093 (at some `m ≥ 1`). -/
theorem main : ∀ n : ℕ, ∃ m : ℕ, 1 ≤ m ∧ z m = n := by
  sorry

end OMA.S_oeis_a111364
