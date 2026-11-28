import Mathlib

/-!
# A096732: Determinant of the n x n matrix m(i,j) = i^j * j^i

Source: https://oeis.org/A096732
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) = det(Mn) where Mn is the n x n matrix with entries m(i,j) = i^j * j^i (1 <= i, j <= n).
Conjecture: lim_{n -> oo} a(n)^(1/n^2) / n = 2 * exp(-3/2).
-/

namespace OMA.S_oeis_a096732

def M (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ((i.val + 1 : ℝ) ^ (j.val + 1)) * ((j.val + 1 : ℝ) ^ (i.val + 1))

noncomputable def a (n : ℕ) : ℝ :=
  (M n).det

theorem main :
    Filter.Tendsto
      (fun n : ℕ => (a n) ^ (1 / ((n : ℝ) ^ 2)) / (n : ℝ))
      Filter.atTop (nhds (2 * Real.exp (-3 / 2 : ℝ))) := by
  sorry

end OMA.S_oeis_a096732
