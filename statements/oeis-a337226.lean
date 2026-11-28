import Mathlib

/-!
# A337226: Lexicographically earliest sequence with at most one j such that a(j) = a(j+k)

Source: https://oeis.org/A337226
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A337226: Lexicographically earliest sequence of positive integers with the property
that, for all k > 0, there is at most one j such that a(j) = a(j+k).

Statement:
Conjecture: For all k > 0, there is exactly one j such that a(j) = a(j+k).

Conventions:
- Sequences are 0-indexed (`a : ℕ → ℕ`) of positive integers (`∀ n, 1 ≤ a n`).
-/

namespace OMA.S_oeis_a337226

/-- Positive integer sequence where each gap `k > 0` has at most one index `j` with `a j = a (j + k)`. -/
def AtMostOneGapMatch (a : ℕ → ℕ) : Prop :=
  (∀ n : ℕ, 1 ≤ a n) ∧
  ∀ k : ℕ, 0 < k → ∀ j₁ j₂ : ℕ, a j₁ = a (j₁ + k) → a j₂ = a (j₂ + k) → j₁ = j₂

/-- `a` is the lexicographically earliest sequence satisfying `AtMostOneGapMatch`. -/
def IsLexEarliest (a : ℕ → ℕ) : Prop :=
  AtMostOneGapMatch a ∧
  ∀ n m : ℕ, 1 ≤ m → m < a n →
    ∃ k j : ℕ, 0 < k ∧ k ≤ n ∧ a (n - k) = m ∧ j + k < n ∧ a j = a (j + k)

theorem main :
    ∀ a : ℕ → ℕ, IsLexEarliest a → ∀ k : ℕ, 0 < k → ∃! j : ℕ, a j = a (j + k) := by
  sorry

end OMA.S_oeis_a337226
