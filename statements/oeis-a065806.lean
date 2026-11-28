import Mathlib

/-!
# A065806: A pseudo-random sequence

Source: https://oeis.org/A065806
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Offset 1; the first terms are `2, 0, 4, 0, 5, 2, 8, 0, 7, 3, 8, 10, ...`. Definition (from the
entry's programs): start with `b(i) = i` for all integers `i`; for `i = 0, 1, 2, …` let
`j = b(i) - b(i-1)`, output `a(i+1) = j + 1`, and swap the values `b(i)` and `b(j)`.

The entry conjectures:
1. `-1 < a(n) < n + 2`;
2. if `a(n) = n + 1` then `a(n+1) = 0`;
3. all integers `> 1` occur in the sequence;
4. for each `c ∈ [0, 1]` there is a subsequence `a(i_j)` with `(a(i_j) + 1)/(i_j + 3) → c`.
This file states all four (as a conjunction), for `n ≥ 1`.
-/

namespace OMA.S_oeis_a065806

/-- The array `b` before step `i`. -/
def B : ℕ → ℤ → ℤ
  | 0 => id
  | i + 1 => B i ∘ Equiv.swap (i : ℤ) (B i i - B i (i - 1))

/-- A065806 (meaningful for `n ≥ 1`). -/
def a (n : ℕ) : ℤ := B (n - 1) (n - 1 : ℕ) - B (n - 1) ((n - 1 : ℕ) - 1) + 1

theorem main :
    (∀ n : ℕ, 1 ≤ n → -1 < a n ∧ a n < n + 2) ∧
    (∀ n : ℕ, 1 ≤ n → a n = n + 1 → a (n + 1) = 0) ∧
    (∀ m : ℤ, 1 < m → ∃ n : ℕ, 1 ≤ n ∧ a n = m) ∧
    (∀ c : ℝ, c ∈ Set.Icc (0 : ℝ) 1 → ∃ i : ℕ → ℕ, StrictMono i ∧ (∀ j, 1 ≤ i j) ∧
      Filter.Tendsto (fun j => ((a (i j) : ℝ) + 1) / ((i j : ℝ) + 3)) Filter.atTop (nhds c)) := by
  sorry

end OMA.S_oeis_a065806
