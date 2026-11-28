import Mathlib

/-!
# A077373: Fibonacci numbers whose external digits as well as internal digits form a Fibonacci number.

Source: https://oeis.org/A077373
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: sequence is finite. Is there any term > 89 in this sequence?
-/

namespace OMA.S_oeis_a077373

/-- `m` is a Fibonacci number. -/
def isFib (m : ℕ) : Prop :=
  ∃ k : ℕ, Nat.fib k = m

/-- `m` is a Fibonacci number whose external digits and internal digits both form Fibonacci numbers. -/
def isGoodFib (m : ℕ) : Prop :=
  isFib m ∧
  let d := (Nat.digits 10 m).length
  2 ≤ d ∧
  isFib (10 * (m / 10 ^ (d - 1)) + m % 10) ∧
  isFib ((m % 10 ^ (d - 1)) / 10)

theorem main :
    { m : ℕ | isGoodFib m }.Finite := by sorry

end OMA.S_oeis_a077373
