import Mathlib

/-!
# A097563: Least integer expressible as a sum of distinct positive squares in exactly n ways

Source: https://oeis.org/A097563
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

a(n) is the least integer that can be written as a sum of zero or more distinct positive squares
in exactly n ways, or -1 if no such number exists.
Conjecture: For n > 34189857569982621, this sequence is the integers > 37163, in order,
interspersed with -1s.
-/

namespace OMA.S_oeis_a097563

noncomputable def numReps (k : ℕ) : ℕ :=
  Set.ncard {S : Finset ℕ | (∀ x ∈ S, 0 < x) ∧ S.sum (fun x => x ^ 2) = k}

noncomputable def a (n : ℕ) : ℤ :=
  open Classical in
  if ∃ k : ℕ, numReps k = n then
    ((sInf {k : ℕ | numReps k = n} : ℕ) : ℤ)
  else
    -1

theorem main :
    (∀ k : ℕ, 37163 < k → ∃ n : ℕ, 34189857569982621 < n ∧ a n = (k : ℤ)) ∧
    (∀ n : ℕ, 34189857569982621 < n → a n = -1 ∨ 37163 < a n) ∧
    (∀ n₁ n₂ : ℕ, 34189857569982621 < n₁ → n₁ < n₂ →
      a n₁ ≠ -1 → a n₂ ≠ -1 → a n₁ < a n₂) := by
  sorry

end OMA.S_oeis_a097563
