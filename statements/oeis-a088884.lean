import Mathlib

/-!
# OEIS A088884: primes `p` with `(p ∥ rev p) - 2` prime

Source: https://oeis.org/A088884
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A088884 lists the primes `p` such that the concatenation of `p` with its digit reversal, minus
`2`, is prime. Conjecture (OEIS entry): except for `3`, all these primes are of the form `6k - 1`.

Conventions:
* For `p` with `L` decimal digits, `p ∥ rev(p) = p · 10^L + rev(p)`, where `rev` reverses the
  decimal digits.
-/

namespace OMA.S_oeis_a088884

/-- Decimal digit reversal. -/
def rev (m : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 m).reverse

/-- `p ∥ rev p`. -/
def cat (p : ℕ) : ℕ := p * 10 ^ (Nat.digits 10 p).length + rev p

/-- Except for `3`, such primes are `≡ 5 (mod 6)`. -/
theorem main : ∀ p : ℕ, p.Prime → (cat p - 2).Prime → p ≠ 3 → p % 6 = 5 := by
  sorry

end OMA.S_oeis_a088884
