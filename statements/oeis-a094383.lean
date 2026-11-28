import Mathlib

/-!
# A094383: Primes p such that d>0 exists and p-d, p-2*d and p-3*d are also primes.

Source: https://oeis.org/A094383
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture: only 25 primes are not in the sequence, namely
2, 3, 5, 7, 11, 13, 17, 19, 31, 37, 47, 61, 67, 71, 73, 89, 109, 137, 179, 211, 277, 337, 379, 499, 557.
-/

namespace OMA.S_oeis_a094383

/-- `p` is the largest term of a 4-term arithmetic progression of primes. -/
def isTerm (p : ℕ) : Prop :=
  p.Prime ∧ ∃ d : ℕ, 0 < d ∧ 3 * d < p ∧
    (p - d).Prime ∧ (p - 2 * d).Prime ∧ (p - 3 * d).Prime

/-- The 25 conjectured exceptional primes. -/
def exceptions : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 31, 37, 47, 61, 67, 71, 73, 89, 109, 137, 179, 211, 277, 337, 379, 499, 557}

theorem main :
    ∀ p : ℕ, p.Prime → (¬ isTerm p ↔ p ∈ exceptions) := by
  sorry

end OMA.S_oeis_a094383
