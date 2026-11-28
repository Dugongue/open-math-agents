import Mathlib

/-!
# A112302: Lerch transcendent recurrence limit for the nested radical constant

Source: https://oeis.org/A112302
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Title: A112302: Decimal expansion of quadratic recurrence constant
sqrt(1 * sqrt(2 * sqrt(3 * sqrt(4 * ...)))).

Statement:
From Johannes W. Meijer, Jun 27 2016: With Phi(z, p, q) the Lerch transcendent, define
LP(n) = (1/n) * sum(Phi(1/2, n-k, 1) * LP(k), k=0..n-1), with LP(0) = 1.
Conjecture: Lim_{n -> infinity} LP(n) = A112302.

Conventions:
- `A112302 = Product_{k >= 1} k^(1 / 2^k)`.
- `Phi(z, s, 1) = Sum_{m >= 0} z^m / (m + 1)^s`.
-/

namespace OMA.S_oeis_a112302

/-- The Lerch transcendent `Phi(z, s, 1) = Sum_{m >= 0} z^m / (m + 1)^s`. -/
noncomputable def lerchPhi1 (z : ℝ) (s : ℕ) : ℝ :=
  ∑' (m : ℕ), z ^ m / ((m + 1 : ℝ) ^ s)

/-- Meijer's recurrence `LP(0) = 1`, `LP(n) = (1/n) * Sum_{k=0..n-1} Phi(1/2, n-k, 1) * LP(k)`. -/
noncomputable def LP : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
    (1 / (n + 1 : ℝ)) * ∑ k : Fin (n + 1), lerchPhi1 (1 / 2) (n + 1 - k.val) * LP k.val
decreasing_by all_goals (simp_wf; omega)

/-- The quadratic recurrence constant `sqrt(1 * sqrt(2 * sqrt(3 * ...))) = Prod_{k>=1} k^(2^(-k))`. -/
noncomputable def nestedRadicalConst : ℝ :=
  ∏' (k : ℕ), ((k + 1 : ℝ)) ^ ((1 / 2 : ℝ) ^ (k + 1))

theorem main :
    Filter.Tendsto LP Filter.atTop (nhds nestedRadicalConst) := by
  sorry

end OMA.S_oeis_a112302
