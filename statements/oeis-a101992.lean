import Mathlib

/-!
# A101992: Numerator of Sum_{i=2..n} (-1)^i/(i*phi(i)).

Source: https://oeis.org/A101992
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: The series `∑_{i >= 2} (-1)^i / (i * phi(i))` converges to a finite limit.
-/

namespace OMA.S_oeis_a101992

/-- The `n`-th partial sum `∑_{i=2}^n (-1)^i / (i * φ(i))`. -/
noncomputable def partialSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 2 n, ((-1 : ℝ) ^ i) / ((i : ℝ) * (Nat.totient i : ℝ))

theorem main :
    ∃ L : ℝ, Filter.Tendsto partialSum Filter.atTop (nhds L) := by
  sorry

end OMA.S_oeis_a101992
