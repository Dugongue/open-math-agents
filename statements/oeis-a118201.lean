import Mathlib

/-!
# OEIS A118201: a Recamán-like sequence with distinct differences

Source: https://oeis.org/A118201
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(0) = 0`; `a(n+1) = a(n) - d` or `a(n) + d`, where `a(n+1)` must be positive and must not have
occurred before; `d` is the smallest positive integer for which this is possible and which is not
an earlier difference `|a(m+1) - a(m)|`; if both `a(n) - d` and `a(n) + d` are new, take
`a(n) - d`. Conjecture (in the entry): every nonnegative integer occurs.

Implementation: `hist n` holds the terms `a(0..n)` and the differences used so far. The search
for `d` is bounded by `sum + 2`: `d = sum + 1` (sum of the terms so far) always qualifies, since
`a(n) + d` then exceeds every earlier term and every earlier difference is `≤` that sum.
-/

namespace OMA.S_oeis_a118201

/-- `d` is admissible after the terms `h` (last term `x`) with used differences `D`. -/
def ok (h D : List ℕ) (x d : ℕ) : Prop :=
  0 < d ∧ d ∉ D ∧ ((d < x ∧ x - d ∉ h) ∨ x + d ∉ h)

instance (h D : List ℕ) (x d : ℕ) : Decidable (ok h D x d) := by
  unfold ok; infer_instance

/-- The smallest admissible difference. -/
def nextD (h D : List ℕ) (x : ℕ) : ℕ :=
  ((List.range (h.sum + 2)).find? fun d => decide (ok h D x d)).getD (h.sum + 1)

/-- The next term from last term `x` and difference `d`. -/
def nextTerm (h : List ℕ) (x d : ℕ) : ℕ :=
  if d < x ∧ x - d ∉ h then x - d else x + d

/-- Terms `a(0), …, a(n)` (with the last one tracked) and the differences used. -/
def hist : ℕ → List ℕ × ℕ × List ℕ
  | 0 => ([0], 0, [])
  | n + 1 =>
    let h := (hist n).1
    let x := (hist n).2.1
    let D := (hist n).2.2
    let d := nextD h D x
    let y := nextTerm h x d
    (h ++ [y], y, D ++ [d])

/-- `a(n)`. -/
def a (n : ℕ) : ℕ := (hist n).2.1

/-- Every nonnegative integer occurs in the sequence. -/
theorem main : ∀ m : ℕ, ∃ n : ℕ, a n = m := by
  sorry

end OMA.S_oeis_a118201
