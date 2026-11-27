import Mathlib

/-!
# OEIS A136032: Mersenne composites are squarefree?

Source: https://oeis.org/A136032
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A136032 gives the number of prime factors (with multiplicity) of the Mersenne composites
`2^p - 1` (`p` prime, `2^p - 1` composite). The entry refers to the conjecture that all Mersenne
composites are squarefree; `main` states it.
-/

namespace OMA.S_oeis_a136032

/-- For every prime `p`, the Mersenne number `2^p - 1` is squarefree. -/
theorem main : ∀ p : ℕ, p.Prime → Squarefree (2 ^ p - 1) := by
  sorry

end OMA.S_oeis_a136032
