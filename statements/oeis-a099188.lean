import Mathlib

/-!
# A099188: a(n) = 2*ceiling(n/sqrt(2)).

Source: https://oeis.org/A099188
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecturally, length of shortest polygonal path from (0,0) to (n,n) with integer vertices
and integer edges.
-/

namespace OMA.S_oeis_a099188

/-- Predicate asserting that two integer lattice points are at integer Euclidean distance `d`. -/
def IsIntDist (p q : ℤ × ℤ) (d : ℕ) : Prop :=
  (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2 = (d : ℤ) ^ 2

/-- A valid polygonal path with integer vertices and integer edge lengths from `p` to `q`
of total length `L`. -/
inductive ValidPath : ℤ × ℤ → ℤ × ℤ → ℕ → Prop
  | nil (p : ℤ × ℤ) : ValidPath p p 0
  | cons {p q r : ℤ × ℤ} {d L : ℕ} :
      IsIntDist p q d → ValidPath q r L → ValidPath p r (d + L)

/-- The conjectured shortest path length `2 * ⌈n / √2⌉`. -/
noncomputable def a (n : ℕ) : ℕ :=
  2 * Nat.ceil ((n : ℝ) / Real.sqrt 2)

theorem main :
    ∀ n : ℕ,
      ValidPath (0, 0) ((n : ℤ), (n : ℤ)) (a n) ∧
      ∀ L : ℕ, ValidPath (0, 0) ((n : ℤ), (n : ℤ)) L → a n ≤ L := by
  sorry

end OMA.S_oeis_a099188
