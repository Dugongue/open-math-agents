import Mathlib

/-!
# A108315: Composite numbers n such that a^v + b^v + c^v + ... is prime, where a*b*c*... is the prime factorization of n and v is the number of prime factors.

Source: https://oeis.org/A108315
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Some consecutive terms are (74,75) (152,153) (325,326) ...
Conjecture: there are infinitely many consecutive values.
-/

namespace OMA.S_oeis_a108315

/-- `n` is a composite number whose prime factors (with multiplicity `v`) satisfy
`∑ p^v` is prime. -/
def isTerm (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧
    ((n.primeFactorsList.map (fun p => p ^ n.primeFactorsList.length)).sum).Prime

theorem main :
    {n : ℕ | isTerm n ∧ isTerm (n + 1)}.Infinite := by
  sorry

end OMA.S_oeis_a108315
