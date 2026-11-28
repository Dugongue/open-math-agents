import Mathlib

/-!
# Quadrisecants of wild knots

Source: https://en.wikipedia.org/wiki/Quadrisecant
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture: every wild knot has infinitely many quadrisecants.

Conventions:
* A knot is a subset `K` of `ℝ³` homeomorphic to the circle.
* A polygonal knot is a knot that is a finite union of segments. `K` is tame when some
  homeomorphism of `ℝ³` maps it onto a polygonal knot, and wild otherwise.
* A quadrisecant of `K` is a line (an affine subspace of dimension `1`) meeting `K` in at least
  four distinct points.
-/

namespace OMA.S_wp_quadrisecants_of_wild_knots

/-- Euclidean `3`-space. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- `K` is a knot. -/
def IsKnot (K : Set E) : Prop := Nonempty (K ≃ₜ Circle)

/-- `K` is a polygonal knot. -/
def IsPolygonalKnot (K : Set E) : Prop :=
  IsKnot K ∧ ∃ s : Finset (E × E), K = ⋃ p ∈ s, segment ℝ p.1 p.2

/-- `K` is a tame knot. -/
def IsTame (K : Set E) : Prop :=
  ∃ h : E ≃ₜ E, IsPolygonalKnot (h '' K)

/-- The quadrisecants of `K`. -/
def quadrisecants (K : Set E) : Set (AffineSubspace ℝ E) :=
  {L | Module.finrank ℝ L.direction = 1 ∧ 4 ≤ ((L : Set E) ∩ K).encard}

theorem main : ∀ K : Set E, IsKnot K → ¬ IsTame K → (quadrisecants K).Infinite := by
  sorry

end OMA.S_wp_quadrisecants_of_wild_knots
