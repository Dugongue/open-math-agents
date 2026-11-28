import Mathlib

/-!
# Slice-ribbon problem

Source: https://www.openproblemgarden.org/op/slice_ribbon_problem_0
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Fox): every slice knot in `S^3` is a ribbon knot.

Conventions (smooth category). `S^3` is the unit sphere of `ℝ^4` and `B^4` the closed unit ball.
* A knot is a smooth `1`-periodic map `γ : ℝ → ℝ^4` into `S^3`, injective on `[0, 1)` and with
  nowhere-vanishing derivative.
* A slice disc for the knot is a smooth map `f : ℝ^2 → ℝ^4` which on the closed unit disc `D^2`
  is injective with injective derivative (a smooth embedding of `D^2`), maps `D^2` into `B^4`,
  maps exactly the boundary circle into `S^3`, and maps that circle onto the knot.
  The knot is slice if it has a slice disc.
* Ribbon is taken in its standard Morse-theoretic form (equivalent to bounding an immersed disc
  in `S^3` with only ribbon singularities): the knot has a slice disc on which the radial
  function `‖f‖²` has only nondegenerate critical points in the open disc, none of them a local
  maximum.
-/

namespace OMA.S_opg_slice_ribbon_problem_0

open Metric

/-- `ℝ^2`. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)
/-- `ℝ^4`. -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- A smooth knot in the unit sphere `S^3 ⊆ ℝ^4`. -/
def IsKnot (γ : ℝ → E4) : Prop :=
  ContDiff ℝ ⊤ γ ∧ Function.Periodic γ 1 ∧ Set.InjOn γ (Set.Ico 0 1) ∧
    (∀ t, deriv γ t ≠ 0) ∧ ∀ t, ‖γ t‖ = 1

/-- `f` is a slice disc for the knot `γ`. -/
def IsSliceDisc (γ : ℝ → E4) (f : E2 → E4) : Prop :=
  ContDiff ℝ ⊤ f ∧ Set.InjOn f (closedBall 0 1) ∧
    (∀ x ∈ closedBall (0 : E2) 1, Function.Injective (fderiv ℝ f x)) ∧
    (∀ x ∈ closedBall (0 : E2) 1, ‖f x‖ ≤ 1) ∧
    (∀ x ∈ closedBall (0 : E2) 1, ‖f x‖ = 1 ↔ ‖x‖ = 1) ∧
    f '' sphere 0 1 = Set.range γ

/-- The radial function `‖f‖²` pulled back to the disc. -/
noncomputable def radial (f : E2 → E4) : E2 → ℝ := fun x => ‖f x‖ ^ 2

/-- `x` is a nondegenerate critical point of `h`: the derivative vanishes and the Hessian
bilinear form is nondegenerate. -/
def IsNondegCrit (h : E2 → ℝ) (x : E2) : Prop :=
  fderiv ℝ h x = 0 ∧ ∀ v : E2, (∀ w : E2, fderiv ℝ (fderiv ℝ h) x v w = 0) → v = 0

/-- `f` is a ribbon disc: a slice disc whose radial function is Morse in the open disc with no
local maxima there. -/
def IsRibbonDisc (γ : ℝ → E4) (f : E2 → E4) : Prop :=
  IsSliceDisc γ f ∧
    ∀ x ∈ ball (0 : E2) 1, fderiv ℝ (radial f) x = 0 →
      IsNondegCrit (radial f) x ∧ ¬ IsLocalMax (radial f) x

/-- Every slice knot is ribbon. -/
theorem main :
    ∀ γ : ℝ → E4, IsKnot γ → (∃ f, IsSliceDisc γ f) → ∃ f, IsRibbonDisc γ f := by
  sorry

end OMA.S_opg_slice_ribbon_problem_0
