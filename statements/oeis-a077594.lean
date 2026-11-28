import Mathlib

/-!
# A077594: Smallest number whose Reverse and Add! trajectory (presumably) contains exactly n palindromes, or -1 if there is no such number.

Source: https://oeis.org/A077594
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture 2: There is no k > 0 such that the trajectory of k contains more than twelve
palindromes, i.e. a(n) = -1 for n > 12.
-/

namespace OMA.S_oeis_a077594

/-- One Reverse-and-Add step in base 10. -/
def revAdd10 (n : ℕ) : ℕ :=
  n + Nat.ofDigits 10 (Nat.digits 10 n).reverse

/-- Predicate that `n` is a base-10 palindrome. -/
def isPalBase10 (n : ℕ) : Prop :=
  (Nat.digits 10 n).reverse = Nat.digits 10 n

theorem main :
    ∀ k : ℕ, 0 < k → ∀ S : Finset ℕ,
      (∀ i ∈ S, isPalBase10 (Nat.iterate revAdd10 i k)) → S.card ≤ 12 := by sorry

end OMA.S_oeis_a077594
