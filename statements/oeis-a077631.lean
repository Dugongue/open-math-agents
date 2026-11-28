import Mathlib

/-!
# A077631: Sum of terms in periodic part of continued fraction expansion of square root of -1 + 3^n.

Source: https://oeis.org/A077631
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

From Benoit Cloitre, Nov 28 2002: a(2n) = 2*3^n - 1.
Conjecture: if n > 1, sqrt(3^(2n+1)) < a(2n+1) < sqrt((2n+1)*3^(2n+1)).
-/

namespace OMA.S_oeis_a077631

/-- One step of the standard integer algorithm for the continued fraction of `√D`. -/
def cfStep (D a0 : ℕ) (st : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let (m, d, a) := st
  let m' := d * a - m
  let d' := (D - m' * m') / d
  let a' := (a0 + m') / d'
  (m', d', a')

/-- The `k`-th partial quotient in the simple continued fraction of `√D`. -/
def cfTerm (D k : ℕ) : ℕ :=
  let a0 := Nat.sqrt D
  (Nat.iterate (cfStep D a0) k (0, 1, a0)).2.2

/-- The period length of the continued fraction expansion of `√D` (for non-square `D`). -/
noncomputable def cfPeriod (D : ℕ) : ℕ :=
  sInf { k : ℕ | 1 ≤ k ∧ cfTerm D k = 2 * Nat.sqrt D }

/-- Sum of the terms in the periodic part of the continued fraction of `√D`. -/
noncomputable def cfPeriodSum (D : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 (cfPeriod D), cfTerm D k

theorem main :
    ∀ n : ℕ, 1 < n →
      Real.sqrt ((3 : ℝ) ^ (2 * n + 1)) < (cfPeriodSum (3 ^ (2 * n + 1) - 1) : ℝ) ∧
      (cfPeriodSum (3 ^ (2 * n + 1) - 1) : ℝ) <
        Real.sqrt (((2 * n + 1 : ℝ) * (3 : ℝ) ^ (2 * n + 1))) := by sorry

end OMA.S_oeis_a077631
