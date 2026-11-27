import Mathlib

/-!
# OEIS A144264: equal prime counts between consecutive squares

Source: https://oeis.org/A144264
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A144264 lists the `k` with `A014085(k) = A014085(k+1)`, where A014085(k) is the number of primes
between `k²` and `(k+1)²`. Conjecture (OEIS entry): the sequence is infinite.
-/

namespace OMA.S_oeis_a144264

/-- Number of primes between `k²` and `(k+1)²`. -/
def c (k : ℕ) : ℕ := ((Finset.Ioo (k ^ 2) ((k + 1) ^ 2)).filter Nat.Prime).card

/-- Infinitely many `k` with `c(k) = c(k+1)`. -/
theorem main : {k : ℕ | c k = c (k + 1)}.Infinite := by
  sorry

end OMA.S_oeis_a144264
