import Mathlib

/-!
# A107742: G.f.: Product{j>=1} Product{i>=1} (1 + x^(i*j)).

Source: https://oeis.org/A107742
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: log(a(n)) ~ Pi*sqrt(n*log(n)/6).
-/

namespace OMA.S_oeis_a107742

/-- The coefficient `[x^n]` of `∏_{j ≥ 1} ∏_{i ≥ 1} (1 + x^(i * j))`. -/
def a (n : ℕ) : ℕ :=
  (((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).powerset).filter
    (fun S => ∑ p ∈ S, p.1 * p.2 = n)).card

theorem main :
    Filter.Tendsto
      (fun n : ℕ =>
        Real.log (a n : ℝ) / (Real.pi * Real.sqrt ((n : ℝ) * Real.log (n : ℝ) / 6)))
      Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a107742
