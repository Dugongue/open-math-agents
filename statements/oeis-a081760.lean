import Mathlib

/-!
# OEIS A081760: Landau's constant

Source: https://oeis.org/A081760
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`Γ(1/3) Γ(5/6) / Γ(1/6) = 0.5432…` is conjectured to be the value of Landau's constant `L`.

Conventions:
* Landau's constant: for `f` holomorphic on the open unit disc `𝔻` with `f'(0) = 1`, let `R(f)` be
  the supremum of the radii of open discs contained in `f(𝔻)`; then `L = inf_f R(f)`.
  `R(f)` is written as `sSup {r | ∃ c, ball c r ⊆ f '' 𝔻}` (with `r ≥ 0`).
-/

namespace OMA.S_oeis_a081760

open Metric

/-- The open unit disc. -/
def D : Set ℂ := ball 0 1

/-- `R(f)`: the supremum of radii of discs contained in `f(𝔻)`. -/
noncomputable def R (f : ℂ → ℂ) : ℝ := sSup {r : ℝ | 0 ≤ r ∧ ∃ c : ℂ, ball c r ⊆ f '' D}

/-- Landau's constant. -/
noncomputable def landau : ℝ :=
  sInf {x : ℝ | ∃ f : ℂ → ℂ, DifferentiableOn ℂ f D ∧ deriv f 0 = 1 ∧ x = R f}

/-- `L = Γ(1/3) Γ(5/6) / Γ(1/6)`. -/
theorem main : landau = Real.Gamma (1 / 3) * Real.Gamma (5 / 6) / Real.Gamma (1 / 6) := by
  sorry

end OMA.S_oeis_a081760
