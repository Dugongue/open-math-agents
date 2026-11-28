import Mathlib

/-!
# A101363: High-multiplicity interior diagonal intersections in regular 30k-gons

Source: https://oeis.org/A101363
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Title: A101363: In the interior of a regular 2n-gon with all diagonals drawn, the number of
points where exactly three diagonals intersect.

Statement:
An n-gon with n = 30k has 5n points where 6 or 7 diagonals meet and no points where more than
7 diagonals meet; if k is odd, then 6 diagonals meet in each of 4n points and 7 diagonals meet
in each of n points; if k is even, then no groups of exactly 6 diagonals meet in a point,
while exactly 7 diagonals meet in each of 5n points.

Conventions:
- Vertices of the regular `n`-gon are the `n`-th roots of unity `exp(2*pi*i*j/n)` in `ℂ`.
- A diagonal is an unordered pair `{j, l}` of non-adjacent distinct vertices (`Fin n`),
  and its open segment consists of convex combinations `(1 - t) * v_j + t * v_l` for `t ∈ (0, 1)`.
- The interior of the regular `n`-gon consists of all points `p` lying on at least one open
  diagonal segment (in particular, not on the boundary or vertices).
-/

namespace OMA.S_oeis_a101363

/-- The `j`-th vertex of the regular `n`-gon on the unit circle in `ℂ`. -/
noncomputable def vertex (n : ℕ) (j : Fin n) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (j.val : ℂ) / (n : ℂ))

/-- `j` and `l` form a diagonal (non-adjacent distinct vertices) of the regular `n`-gon. -/
def IsDiagonal (n : ℕ) (j l : Fin n) : Prop :=
  j.val < l.val ∧ l.val - j.val ≠ 1 ∧ j.val + n - l.val ≠ 1

/-- Point `p` lies on the open segment between vertices `j` and `l`. -/
def OnOpenDiagonal (n : ℕ) (p : ℂ) (j l : Fin n) : Prop :=
  IsDiagonal n j l ∧
  ∃ t : ℝ, 0 < t ∧ t < 1 ∧ p = ((1 - t : ℝ) : ℂ) * vertex n j + (t : ℂ) * vertex n l

/-- Number of diagonals of the regular `n`-gon passing through `p` in their open interior. -/
noncomputable def diagMult (n : ℕ) (p : ℂ) : ℕ :=
  {pair : Fin n × Fin n | OnOpenDiagonal n p pair.1 pair.2}.ncard

theorem main :
    ∀ k : ℕ, 1 ≤ k →
      let n := 30 * k
      (∀ p : ℂ, diagMult n p ≤ 7) ∧
      ({p : ℂ | diagMult n p = 6 ∨ diagMult n p = 7}.ncard = 5 * n) ∧
      (Odd k →
        {p : ℂ | diagMult n p = 6}.ncard = 4 * n ∧
        {p : ℂ | diagMult n p = 7}.ncard = n) ∧
      (Even k →
        {p : ℂ | diagMult n p = 6}.ncard = 0 ∧
        {p : ℂ | diagMult n p = 7}.ncard = 5 * n) := by
  sorry

end OMA.S_oeis_a101363
