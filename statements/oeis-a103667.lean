import Mathlib

/-!
# A103667: Primes p with largest prime factor of p-1 greater than that of p+1

Source: https://oeis.org/A103667
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Primes p such that the largest prime divisor of p - 1 is greater than the largest prime
divisor of p + 1.
Conjecture: This sequence has positive relative density in the primes.
-/

namespace OMA.S_oeis_a103667

open Filter Topology

/-- Largest prime factor of `m` (0 if `m ≤ 1`). -/
def lpf (m : ℕ) : ℕ :=
  m.primeFactors.sup id

/-- Number of primes `p ≤ N` such that `lpf(p - 1) > lpf(p + 1)`. -/
def countGood (N : ℕ) : ℕ :=
  ((Finset.Icc 2 N).filter (fun p => Nat.Prime p ∧ lpf (p + 1) < lpf (p - 1))).card

/-- Number of primes `p ≤ N`. -/
def primePi (N : ℕ) : ℕ :=
  ((Finset.Icc 2 N).filter Nat.Prime).card

theorem main :
    ∃ d : ℝ, 0 < d ∧
      Tendsto (fun N : ℕ => (countGood N : ℝ) / (primePi N : ℝ)) atTop (𝓝 d) := by
  sorry

end OMA.S_oeis_a103667
