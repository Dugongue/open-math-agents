import Mathlib

/-!
# OEIS A063897: `k - F_j` prime for the first Fermat numbers

Source: https://oeis.org/A063897
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the least `k` such that `k - F_j` is prime for all `j = 0, …, n`, where
`F_j = 2^(2^j) + 1` are the Fermat numbers (A000215). The entry notes that the prime `k`-tuples
conjecture implies that the sequence is infinite, i.e. `a(n)` exists for every `n`; `main` states
this existence.
-/

namespace OMA.S_oeis_a063897

/-- The Fermat number `F_j`. -/
def F (j : ℕ) : ℕ := 2 ^ 2 ^ j + 1

/-- For every `n` some `k` has `k - F_j` prime for all `j ≤ n`. -/
theorem main : ∀ n : ℕ, ∃ k : ℕ, ∀ j ≤ n, F j < k ∧ (k - F j).Prime := by
  sorry

end OMA.S_oeis_a063897
