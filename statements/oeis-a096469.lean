import Mathlib

/-!
# A096469: Smallest m such that concatenation of m^0, m^1, ..., m^n is prime

Source: https://oeis.org/A096469
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) is the smallest number m such that the decimal concatenation of the n+1 numbers
m^0, m^1, ..., m^(n-1), m^n is a prime.
Conjecture: This sequence is infinite (i.e. such m exists for every n >= 1).
-/

namespace OMA.S_oeis_a096469

def concatPowers (m n : ℕ) : ℕ :=
  Nat.ofDigits 10 (((List.range (n + 1)).flatMap (fun k => (Nat.digits 10 (m ^ k)).reverse)).reverse)

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 1 ≤ m ∧ Nat.Prime (concatPowers m n) := by
  sorry

end OMA.S_oeis_a096469
