import Mathlib

/-!
# OEIS A084653: primitive-factor base-2 pseudoprimes

Source: https://oeis.org/A084653
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A084653 lists the Fermat base-2 pseudoprimes whose prime factors divide no smaller pseudoprime.
Conjecture (OEIS entry, tested below `10^15`): all of them have only two prime factors.

Conventions:
* A base-2 pseudoprime is a composite `n` with `n ∣ 2^(n-1) - 1`. 'Two prime factors' is read
  with multiplicity (`Ω(n) = 2`, i.e. `n = pq` or `p²`).
-/

namespace OMA.S_oeis_a084653

open ArithmeticFunction

/-- `n` is a Fermat base-2 pseudoprime. -/
def Psp (n : ℕ) : Prop := 1 < n ∧ ¬ n.Prime ∧ n ∣ 2 ^ (n - 1) - 1

/-- Every term has exactly two prime factors. -/
theorem main : ∀ n : ℕ, Psp n → (∀ p ∈ n.primeFactors, ∀ m < n, Psp m → ¬ p ∣ m) →
    cardFactors n = 2 := by
  sorry

end OMA.S_oeis_a084653
