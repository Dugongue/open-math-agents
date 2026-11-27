import Mathlib

/-!
# OEIS A068405: one more distinct prime factor than the squarefree successor

Source: https://oeis.org/A068405
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A068405 lists the `k` such that `k + 1` is squarefree and composite and `k` has one more distinct
prime factor than `k + 1`. The entry notes that Dickson's conjecture implies the sequence is
infinite; `main` states that it is infinite.
-/

namespace OMA.S_oeis_a068405

/-- The defining property. -/
def P (k : ℕ) : Prop :=
  Squarefree (k + 1) ∧ 1 < k + 1 ∧ ¬ (k + 1).Prime ∧
    k.primeFactors.card = (k + 1).primeFactors.card + 1

/-- The sequence is infinite. -/
theorem main : {k | P k}.Infinite := by
  sorry

end OMA.S_oeis_a068405
