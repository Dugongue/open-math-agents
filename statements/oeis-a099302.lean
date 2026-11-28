import Mathlib

/-!
# A099302: Number of integer solutions to x' = n, where x' is the arithmetic derivative of x.

Source: https://oeis.org/A099302
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

It appears that there are a finite number of even numbers having a given number of solutions
to `x' = n`.
-/

namespace OMA.S_oeis_a099302

/-- The arithmetic derivative of a natural number: `0' = 0`, `1' = 0`, `p' = 1` for prime `p`,
and `(a * b)' = a' * b + a * b'`. -/
def arithDeriv (n : ℕ) : ℕ :=
  if n = 0 then 0 else ∑ p ∈ n.primeFactors, (n / p) * n.factorization p

theorem main :
    ∀ k : ℕ, {n : ℕ | Even n ∧ Set.encard {x : ℕ | arithDeriv x = n} = (k : ℕ∞)}.Finite := by
  sorry

end OMA.S_oeis_a099302
