import Mathlib

/-!
# OEIS A072923: primes of the form `⌊(1 + 1/k)ⁿ⌋`

Source: https://oeis.org/A072923
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of primes of the form `⌊(1 + 1/k)ⁿ⌋`, `1 ≤ k ≤ n`. Conjecture (OEIS entry):
`a(n) ~ C n` with `C = 0.47…`.

Conventions:
* 'Number of primes of the form' counts distinct prime values. `C = 0.47…` is read as
  `[0.47, 0.48)`; `~` is `IsEquivalent`.
-/

namespace OMA.S_oeis_a072923

open Filter Asymptotics

/-- Number of distinct primes among `⌊(1 + 1/k)ⁿ⌋`, `1 ≤ k ≤ n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  (((Finset.Icc 1 n).image fun k : ℕ => ⌊(1 + 1 / (k : ℝ)) ^ n⌋.toNat).filter Nat.Prime).card

/-- `a(n) ~ C n` with `C ∈ [0.47, 0.48)`. -/
theorem main : ∃ C : ℝ, 0.47 ≤ C ∧ C < 0.48 ∧
    IsEquivalent atTop (fun n : ℕ => (a n : ℝ)) (fun n => C * n) := by
  sorry

end OMA.S_oeis_a072923
