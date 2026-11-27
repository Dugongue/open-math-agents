import Mathlib

/-!
# OEIS A129812: consecutive primes whose last digits differ by `6`

Source: https://oeis.org/A129812
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A129812 lists the lesser of two consecutive primes whose last decimal digits differ by `6`.
Conjecture (OEIS entry): the sequence is infinite.

Conventions:
* Consecutive primes are `nth Prime i` and `nth Prime (i + 1)`; 'differ by `6`' is
  `|d₁ - d₂| = 6` for the last digits (`mod 10`).
-/

namespace OMA.S_oeis_a129812

/-- Infinitely many consecutive prime pairs whose last digits differ by `6`. -/
theorem main : {i : ℕ | Int.natAbs ((Nat.nth Nat.Prime i % 10 : ℕ) - (Nat.nth Nat.Prime (i + 1) % 10 : ℕ) : ℤ) = 6}.Infinite := by
  sorry

end OMA.S_oeis_a129812
