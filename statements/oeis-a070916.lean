import Mathlib

/-!
# OEIS A070916: `a(n) a(n-1) - 1` prime, growth constant

Source: https://oeis.org/A070916
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(1) = 1` and `a(n)` is the smallest integer `≥ a(n-1)` such that `a(n) a(n-1) - 1` is prime.
Conjecture (OEIS entry): `lim_{n → ∞} a(n)/(n log n) = C = 1.075…`.

Conventions:
* Indexing from `0` (`a 0 = 1`); the shift does not affect the limit. `C = 1.075…` is read as
  `1.075 ≤ C < 1.076`.
-/

namespace OMA.S_oeis_a070916

open Filter Topology

/-- The greedy sequence. -/
noncomputable def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => sInf {m : ℕ | a n ≤ m ∧ (m * a n - 1).Prime}

/-- `a(n)/(n log n) → C ∈ [1.075, 1.076)`. -/
theorem main : ∃ C : ℝ, 1.075 ≤ C ∧ C < 1.076 ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / (n * Real.log n)) atTop (𝓝 C) := by
  sorry

end OMA.S_oeis_a070916
