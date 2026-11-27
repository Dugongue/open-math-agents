import Mathlib

/-!
# OEIS A067723: palindromes `k` with `φ(k)` a palindrome

Source: https://oeis.org/A067723
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A067723 lists the nontrivial palindromes `k` (at least two digits) such that `φ(k)` is also a
palindrome. Conjecture (OEIS entry): there are no terms with an even number of digits.

Conventions:
* Decimal palindromes: `Nat.digits 10` equal to its reverse.
-/

namespace OMA.S_oeis_a067723

/-- Decimal palindrome. -/
def IsPal (m : ℕ) : Prop := (Nat.digits 10 m).reverse = Nat.digits 10 m

/-- No palindrome with an even (positive) number of digits has palindromic `φ`. -/
theorem main : ∀ k : ℕ, IsPal k → Even (Nat.digits 10 k).length → 10 ≤ k →
    ¬ IsPal (Nat.totient k) := by
  sorry

end OMA.S_oeis_a067723
