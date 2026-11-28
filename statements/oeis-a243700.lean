import Mathlib

/-!
# A243700: Lexicographically earliest sequence of distinct terms with a(1) = 1 and a(n) | sum_{k=1}^{a(n)} a(k)

Source: https://oeis.org/A243700
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: Let `a` be the lexicographically earliest 1-indexed sequence of distinct
positive integers with `a(1) = 1` such that `a(n)` divides `∑_{k=1}^{a(n)} a(k)` for all
`n ≥ 1`. Then the asymptotic ratios `a(n) / n` accumulate along the six slopes
`1, √3/3 + 1, √3/6 + 3/2, √3/3 + 2, √3/6 + 5/2, √3/3 + 3` (i.e., for every `ε > 0`,
`a(n) / n` is eventually within `ε` of one of these six values).
-/

namespace OMA.S_oeis_a243700

open Filter

/-- A valid candidate for A243700 (1-indexed, with `a 0 = 0`). -/
def IsValidA243700 (a : ℕ → ℕ) : Prop :=
  a 0 = 0 ∧ a 1 = 1 ∧
  (∀ n : ℕ, 1 ≤ n → 1 ≤ a n) ∧
  (∀ m n : ℕ, 1 ≤ m → 1 ≤ n → a m = a n → m = n) ∧
  (∀ n : ℕ, 1 ≤ n → a n ∣ ∑ k ∈ Finset.Icc 1 (a n), a k)

/-- `a` is the lexicographically earliest valid sequence for A243700. -/
def IsA243700 (a : ℕ → ℕ) : Prop :=
  IsValidA243700 a ∧
  ∀ b : ℕ → ℕ, IsValidA243700 b →
    a = b ∨ ∃ m : ℕ, 1 ≤ m ∧ (∀ k : ℕ, 1 ≤ k → k < m → a k = b k) ∧ a m < b m

/-- The six conjectured asymptotic slopes. -/
noncomputable def sixSlopes : Set ℝ :=
  {1, Real.sqrt 3 / 3 + 1, Real.sqrt 3 / 6 + 3 / 2,
    Real.sqrt 3 / 3 + 2, Real.sqrt 3 / 6 + 5 / 2, Real.sqrt 3 / 3 + 3}

theorem main :
    ∀ a : ℕ → ℕ, IsA243700 a →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop, ∃ s ∈ sixSlopes, |(a n : ℝ) / (n : ℝ) - s| < ε := by
  sorry

end OMA.S_oeis_a243700
