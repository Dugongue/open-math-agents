import Mathlib

/-!
# OEIS A080783: a self-referential walk, asymptotically `3n`

Source: https://oeis.org/A080783
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(1) = 1`, `a(n) = a(n-1) - 1` if `n` is already in the sequence, `a(n) = a(n-1) + 5` otherwise.
It is conjectured that `a(n) ~ 3n`.

Conventions:
* 'Already in the sequence' means `n ∈ {a(1), …, a(n-1)}`. Values are integers (the `-1` steps
  could in principle go below `1`). The terms are generated as a list.
-/

namespace OMA.S_oeis_a080783

open Filter Asymptotics

/-- The terms `a(1), …, a(n)` (for `n ≥ 1`). -/
def terms : ℕ → List ℤ
  | 0 => []
  | 1 => [1]
  | n + 2 =>
    let l := terms (n + 1)
    let prev := l.getLast?.getD 0
    l ++ [if ((n + 2 : ℕ) : ℤ) ∈ l then prev - 1 else prev + 5]

/-- `a(n)`. -/
def a (n : ℕ) : ℤ := (terms n).getLast?.getD 0

/-- `a(n) ~ 3n`. -/
theorem main : IsEquivalent atTop (fun n : ℕ => (a n : ℝ)) (fun n => 3 * (n : ℝ)) := by
  sorry

end OMA.S_oeis_a080783
