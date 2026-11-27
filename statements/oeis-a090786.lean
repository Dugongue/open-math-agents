import Mathlib

/-!
# OEIS A090786: least `k` with `n! + n + k + 1` prime

Source: https://oeis.org/A090786
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the least nonnegative `k` such that `n! + n + k + 1` is prime. Questions (OEIS entry):
is `a(n) + n + 1` (= A037153(n)) also prime for all `n > 2`? Is `b(n) = ∑_{k=0}^{n} a(k)` of
quadratic growth, `b(n) = O(n²)`? `main` states both with the answer yes.

Conventions:
* `a(n) = sInf {k | n! + n + k + 1 prime}` (the set is nonempty since there are infinitely many
  primes).
-/

namespace OMA.S_oeis_a090786

open Filter Asymptotics

/-- `a(n)`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | (n.factorial + n + k + 1).Prime}

/-- `a(n) + n + 1` is prime for `n > 2`, and `∑_{k ≤ n} a(k) = O(n²)`. -/
theorem main : (∀ n : ℕ, 2 < n → (a n + n + 1).Prime) ∧
    (fun n : ℕ => (∑ k ∈ Finset.range (n + 1), (a k : ℝ))) =O[atTop] fun n => (n : ℝ) ^ 2 := by
  sorry

end OMA.S_oeis_a090786
