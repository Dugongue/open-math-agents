import Mathlib

/-!
# A234566: Reciprocal area of smallest triangle formed by grid lines on an n x n grid

Source: https://oeis.org/A234566
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A234566: 1/a(n) is the area of the smallest triangle delimited by 3 lines each passing
through at least 2 points of an n X n unitary spaced grid.

Statement:
Conjecture: sequence is well-defined, i.e., a(n) is an integer for every n > 1.

Conventions:
- The `n x n` unit-spaced grid consists of integer points `(x, y)` with `0 <= x < n` and `0 <= y < n`.
- A grid line is a line in `ℝ^2` passing through at least two distinct grid points.
- Three grid lines delimit a non-degenerate triangle with vertices `p, q, r : ℝ × ℝ` when
  `triangleArea p q r > 0` and each pair `(p, q)`, `(q, r)`, `(r, p)` lies on a grid line.
-/

namespace OMA.S_oeis_a234566

/-- The set of points in the `n x n` unit-spaced integer grid. -/
def GridPoint (n : ℕ) : Set (ℝ × ℝ) :=
  {p | ∃ x y : ℕ, x < n ∧ y < n ∧ p = ((x : ℝ), (y : ℝ))}

/-- Three points in `ℝ^2` are collinear. -/
def Collinear3 (p q r : ℝ × ℝ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (q.2 - p.2) * (r.1 - p.1)

/-- Two points `p, q` lie on a line passing through at least two distinct `n x n` grid points. -/
def IsGridLine (n : ℕ) (p q : ℝ × ℝ) : Prop :=
  ∃ u v : ℝ × ℝ, u ∈ GridPoint n ∧ v ∈ GridPoint n ∧ u ≠ v ∧
    Collinear3 u v p ∧ Collinear3 u v q

/-- The area of the triangle with vertices `p, q, r` in `ℝ^2`. -/
noncomputable def triangleArea (p q r : ℝ × ℝ) : ℝ :=
  |(q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)| / 2

/-- `p, q, r` are the vertices of a non-degenerate triangle delimited by 3 grid lines. -/
def IsGridLineTriangle (n : ℕ) (p q r : ℝ × ℝ) : Prop :=
  0 < triangleArea p q r ∧ IsGridLine n p q ∧ IsGridLine n q r ∧ IsGridLine n r p

theorem main :
    ∀ n : ℕ, 1 < n →
      ∃ a : ℕ, 0 < a ∧
        (∀ p q r : ℝ × ℝ, IsGridLineTriangle n p q r → (1 : ℝ) / (a : ℝ) ≤ triangleArea p q r) ∧
        (∃ p q r : ℝ × ℝ, IsGridLineTriangle n p q r ∧ triangleArea p q r = (1 : ℝ) / (a : ℝ)) := by
  sorry

end OMA.S_oeis_a234566
