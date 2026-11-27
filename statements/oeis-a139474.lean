import Mathlib

/-!
# OEIS A139474: Ramsey's Mersenne-prime criterion

Source: https://oeis.org/A139474
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = ((3 + 2√2)^m - (3 - 2√2)^m)/(4√2)` with `m = 2^(prime(n)-1) - 1`. Conjecture (Ramsey,
2006): `a(n)` is divisible by `2^prime(n) - 1` iff `2^prime(n) - 1` is a Mersenne prime.

Conventions:
* `((3 + 2√2)^m - (3 - 2√2)^m)/(4√2) = b(m)` with `b(0) = 0`, `b(1) = 1`,
  `b(k) = 6 b(k-1) - b(k-2)` (A001109), which is used as the definition. `p` ranges over primes.
-/

namespace OMA.S_oeis_a139474

/-- A001109. -/
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | k + 2 => 6 * b (k + 1) - b k

/-- `2^p - 1 ∣ b(2^(p-1) - 1)` iff `2^p - 1` is prime. -/
theorem main : ∀ p : ℕ, p.Prime →
    (((2 : ℤ) ^ p - 1) ∣ b (2 ^ (p - 1) - 1) ↔ (2 ^ p - 1).Prime) := by
  sorry

end OMA.S_oeis_a139474
