import Mathlib

/-!
# A092193: Number of generations for which prime(n) divides A001008(k) for some k.

Source: https://oeis.org/A092193
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

For any prime p, generation m consists of the numbers p^(m-1) <= k < p^m. The zeroth
generation consists of just the number 0. When there is a k in generation m such that p
divides A001008(k), then that k may generate solutions in generation m+1. It is
conjectured that for all primes there are solutions for only a finite number of generations.
-/

namespace OMA.S_oeis_a092193

def harmonic (k : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / (i : ℚ)

theorem main :
    ∀ p : ℕ, Nat.Prime p →
      {m : ℕ | 1 ≤ m ∧ ∃ k : ℕ, p ^ (m - 1) ≤ k ∧ k < p ^ m ∧
        (p : ℤ) ∣ (harmonic k).num}.Finite := by
  sorry

end OMA.S_oeis_a092193
