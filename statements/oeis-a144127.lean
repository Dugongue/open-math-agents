import Mathlib

/-!
# OEIS A144127: primes among values of the Legendre polynomial `P₆`

Source: https://oeis.org/A144127
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A144127 lists the primes of the form `P₆(n)`, `P₆` the Legendre polynomial of order `6`. The
entry notes the sequence is infinite under Bunyakovsky's conjecture; `main` states that it is
infinite.

Conventions:
* `P₆(x) = (231x⁶ - 315x⁴ + 105x² - 5)/16`; `n` ranges over integers and `P₆(n)` must be a prime
  integer.
-/

namespace OMA.S_oeis_a144127

/-- `P₆(n)` as a rational number. -/
def P6 (n : ℤ) : ℚ := (231 * n ^ 6 - 315 * n ^ 4 + 105 * n ^ 2 - 5) / 16

/-- Infinitely many primes are values of `P₆` at integers. -/
theorem main : {q : ℕ | q.Prime ∧ ∃ n : ℤ, P6 n = q}.Infinite := by
  sorry

end OMA.S_oeis_a144127
