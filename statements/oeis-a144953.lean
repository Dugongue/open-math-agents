import Mathlib

/-!
# OEIS A144953: primes of the form `n³ + 2`

Source: https://oeis.org/A144953
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A144953 lists the primes of the form `n³ + 2`. Hardy–Littlewood's Conjecture K suggests that the
sequence is infinite; `main` states that it is infinite.
-/

namespace OMA.S_oeis_a144953

/-- Infinitely many `n` make `n³ + 2` prime. -/
theorem main : {n : ℕ | (n ^ 3 + 2).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a144953
