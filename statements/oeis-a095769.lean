import Mathlib

/-!
# A095769: a(1)=a(2)=1; a(n)=a(a(a(a(n-1))))+a(n-a(a(a(n-1)))).

Source: https://oeis.org/A095769
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture: lim_{n->oo} a(n)/n = 0.682327803828... (the real positive root of x^3 + x = 1).
-/

namespace OMA.S_oeis_a095769

/-- Predicate characterizing sequences satisfying the A095769 recurrence. -/
def SatisfiesRecurrence (a : ℕ → ℕ) : Prop :=
  a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 1 ∧
    ∀ n : ℕ, 3 ≤ n → a n = a (a (a (a (n - 1)))) + a (n - a (a (a (n - 1))))

theorem main :
    ∀ a : ℕ → ℕ, SatisfiesRecurrence a →
      ∃ r : ℝ, 0 < r ∧ r ^ 3 + r = 1 ∧
        Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ)) Filter.atTop (nhds r) := by
  sorry

end OMA.S_oeis_a095769
