import Mathlib

/-!
# OEIS A106908: primes of the form `4x² + 3xy + 4y²`

Source: https://oeis.org/A106908
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A106908 lists the primes of the form `4x² + 3xy + 4y²` (`x, y` integers). The entry notes that,
according to the Bunyakovsky conjecture, there are infinitely many such primes; `main` states that
there are infinitely many.
-/

namespace OMA.S_oeis_a106908

/-- Infinitely many primes are represented by `4x² + 3xy + 4y²`. -/
theorem main : {p : ℕ | p.Prime ∧ ∃ x y : ℤ, (p : ℤ) = 4 * x ^ 2 + 3 * x * y + 4 * y ^ 2}.Infinite := by
  sorry

end OMA.S_oeis_a106908
