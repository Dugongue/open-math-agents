import Mathlib

/-!
# OEIS A079729: the Kolakoski-(1,2,3) sequence, letter frequencies

Source: https://oeis.org/A079729
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The Kolakoski-(1,2,3) sequence `K` over `{1, 2, 3}` is its own run-length sequence, with run values
cycling `1, 2, 3, 1, 2, 3, …`: `1, 2, 2, 3, 3, 1, 1, 1, 2, 2, 2, 3, …`. Conjecture (OEIS entry):
the frequencies of `1`s, `2`s and `3`s exist and all equal `1/3`.

Conventions:
* Characterisation (indices from `0`): run `i` starts at `s(i)` with `s(0) = 0`,
  `s(i+1) = s(i) + K(i)`, and consists of the value `(i mod 3) + 1`. `main` quantifies over every
  `K` with this property (there is exactly one).
-/

namespace OMA.S_oeis_a079729

open Filter Topology

/-- Run starts. -/
def runStart (K : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => runStart K i + K i

/-- `K` is the Kolakoski-(1,2,3) sequence. -/
def IsKolakoski123 (K : ℕ → ℕ) : Prop :=
  ∀ i j, runStart K i ≤ j → j < runStart K (i + 1) → K j = i % 3 + 1

/-- Each value `1, 2, 3` has frequency `1/3`. -/
theorem main : ∀ K : ℕ → ℕ, IsKolakoski123 K → ∀ v ∈ ({1, 2, 3} : Finset ℕ),
    Tendsto (fun N : ℕ => (((Finset.range N).filter fun j => K j = v).card : ℝ) / N) atTop
      (𝓝 (1 / 3)) := by
  sorry

end OMA.S_oeis_a079729
