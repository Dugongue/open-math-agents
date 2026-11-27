import Mathlib

/-!
# OEIS A109994: Chen primes whose partner is a Sarrus number

Source: https://oeis.org/A109994
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A109994 lists the Chen primes `p` (`p + 2` prime or semiprime) whose partner `p + 2` is a Sarrus
number (a base-2 Fermat pseudoprime). Conjecture (OEIS entry): the sequence is infinite.

Conventions:
* A Sarrus number is a composite `m` with `m ∣ 2^(m-1) - 1`; being composite, a Chen partner
  `p + 2` must then be a semiprime (`Ω = 2`).
-/

namespace OMA.S_oeis_a109994

open ArithmeticFunction

/-- Infinitely many primes `p` have `p + 2` a semiprime base-2 pseudoprime. -/
theorem main : {p : ℕ | p.Prime ∧ cardFactors (p + 2) = 2 ∧ (p + 2) ∣ 2 ^ (p + 1) - 1}.Infinite := by
  sorry

end OMA.S_oeis_a109994
