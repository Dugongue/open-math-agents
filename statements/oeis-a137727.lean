import Mathlib

/-!
# OEIS A137727: final digit of `prime(n) prime(n+1)`

Source: https://oeis.org/A137727
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the final digit of `prime(n) prime(n+1)`; it is `1, 3, 7` or `9` for `n > 3`.
Conjecture (OEIS entry): `1` and `9` appear `17/66` of the time and `3` and `7` appear `8/33` of the
time.

Conventions:
* Frequencies are limits of `#{n < N | a(n) = d}/N` (indices from `0`, `prime` via `Nat.nth`).
-/

namespace OMA.S_oeis_a137727

open Filter Topology

/-- `a(n)`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth Nat.Prime n * Nat.nth Nat.Prime (n + 1) % 10

/-- Asymptotic frequency of the digit `d`. -/
def HasFreq (d : ℕ) (c : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (((Finset.range N).filter fun n => a n = d).card : ℝ) / N) atTop (𝓝 c)

/-- The conjectured frequencies. -/
theorem main : HasFreq 1 (17 / 66) ∧ HasFreq 9 (17 / 66) ∧ HasFreq 3 (8 / 33) ∧ HasFreq 7 (8 / 33) := by
  sorry

end OMA.S_oeis_a137727
