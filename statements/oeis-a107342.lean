import Mathlib

/-!
# A107342: Semiprimes with semiprime digits (digits 4, 6, 9 only).

Source: https://oeis.org/A107342
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: almost all terms (asymptotic density 1) end with 9 and have either
3k+1 or 3k+2 occurrences of the digit 4 for some nonnegative k.
-/

namespace OMA.S_oeis_a107342

/-- `n` is a semiprime (product of two primes, not necessarily distinct). -/
def isSemiprime (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q

/-- `n` is a term of A107342: a semiprime whose base-10 digits are all in `{4, 6, 9}`. -/
def isTerm (n : ℕ) : Prop :=
  isSemiprime n ∧ ∀ d ∈ Nat.digits 10 n, d = 4 ∨ d = 6 ∨ d = 9

/-- `n` ends with the digit `9` and the number of occurrences of digit `4` is not divisible by `3`. -/
def isGood (n : ℕ) : Prop :=
  n % 10 = 9 ∧ ((Nat.digits 10 n).count 4) % 3 ≠ 0

open Classical in
theorem main :
    Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.Icc 1 N).filter (fun n => isTerm n ∧ isGood n)).card : ℝ) /
          (((Finset.Icc 1 N).filter isTerm).card : ℝ))
      Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a107342
