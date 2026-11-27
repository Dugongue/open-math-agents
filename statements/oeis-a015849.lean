import Mathlib

/-!
# OEIS A015849: `φ(n + 9) ∣ σ(n)`

Source: https://oeis.org/A015849
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A015849 lists the `n ≢ 0 (mod 3)` with `φ(n + 9) ∣ σ(n)`. The entry notes that it contains the
primes `p` with `(p + 9)/8` prime, so Dickson's conjecture implies that the sequence is infinite;
`main` states that it is infinite.
-/

namespace OMA.S_oeis_a015849

open ArithmeticFunction

/-- Infinitely many `n ≢ 0 (mod 3)` satisfy `φ(n + 9) ∣ σ(n)`. -/
theorem main : {n : ℕ | 1 ≤ n ∧ n % 3 ≠ 0 ∧ Nat.totient (n + 9) ∣ ArithmeticFunction.sigma 1 n}.Infinite := by
  sorry

end OMA.S_oeis_a015849
