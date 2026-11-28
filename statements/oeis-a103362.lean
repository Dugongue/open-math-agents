import Mathlib

/-!
# A103362: Fraction of primes < 10^n that are full reptend primes approaches Artin's constant

Source: https://oeis.org/A103362
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

The fraction of primes < 10^n that are full reptend primes (primes p for which 10 is a
primitive root modulo p) is conjectured to approach Artin's constant
C = Product_{p prime} (1 - 1 / (p * (p - 1))).
-/

namespace OMA.S_oeis_a103362

open Filter Topology
open scoped Classical

/-- Partial product up to `N` for Artin's constant `∏_{p prime} (1 - 1 / (p * (p - 1)))`. -/
noncomputable def artinPartialProd (N : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
    (1 - 1 / ((p : ℝ) * ((p : ℝ) - 1)))

/-- Fraction of primes `< 10^n` that are full reptend primes (base 10). -/
noncomputable def reptendFrac (n : ℕ) : ℝ :=
  (((Finset.range (10 ^ n)).filter (fun p => Nat.Prime p ∧ orderOf (10 : ZMod p) = p - 1)).card : ℝ) /
    (((Finset.range (10 ^ n)).filter Nat.Prime).card : ℝ)

theorem main :
    ∃ C : ℝ,
      Tendsto artinPartialProd atTop (𝓝 C) ∧
      Tendsto reptendFrac atTop (𝓝 C) := by
  sorry

end OMA.S_oeis_a103362
