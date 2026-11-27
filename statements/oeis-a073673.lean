import Mathlib

/-!
# OEIS A073673: partial products plus one all prime

Source: https://oeis.org/A073673
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A073673 is the rearrangement of the natural numbers obtained greedily so that every partial
product plus `1` is prime: `a(1) = 1`, and `a(n)` is the least number not used so far such that
`a(1) a(2) ⋯ a(n) + 1` is prime. Conjecture (OEIS entry): `n/log n ≪ a(n) ≪ n log n`.

Conventions:
* Indexing from `0` (`a 0 = 1`). The greedy step: `a(n+1)` is the least `m ≥ 1` not among
  `a(0), …, a(n)` with `a(0) ⋯ a(n) · m + 1` prime (`sInf`, `0` if none).
* `n/log n ≪ a(n) ≪ n log n` is: `n/log n = O(a(n))` and `a(n) = O(n log n)` as `n → ∞`.
-/

namespace OMA.S_oeis_a073673

open Filter Asymptotics

/-- The first `n + 1` terms, as a list. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => [1]
  | n + 1 =>
    let l := terms n
    l ++ [sInf {m : ℕ | 1 ≤ m ∧ m ∉ l ∧ (l.prod * m + 1).Prime}]

/-- `a(n)`. -/
noncomputable def a (n : ℕ) : ℕ := (terms n).getLast?.getD 0

/-- `n/log n ≪ a(n) ≪ n log n`. -/
theorem main :
    (fun n : ℕ => (n : ℝ) / Real.log n) =O[atTop] (fun n => (a n : ℝ)) ∧
    (fun n : ℕ => (a n : ℝ)) =O[atTop] (fun n => (n : ℝ) * Real.log n) := by
  sorry

end OMA.S_oeis_a073673
