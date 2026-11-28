import Mathlib

/-!
# A094405: a(1) = 1; a(n) = (sum of previous terms) mod n.

Source: https://oeis.org/A094405
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: For any seed a(1) the sequence "a(n) = (sum of previous terms) mod n"
ends with repeating constant. This is true for a(1) = 1,...,941.
-/

namespace OMA.S_oeis_a094405

/-- `(a(n), sum_{k=1}^n a(k))` for the sequence with seed `a(1) = c` (1-indexed). -/
def state (c : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | 1 => (c, c)
  | n + 2 =>
    let s := (state c (n + 1)).2
    let val := s % (n + 2)
    (val, s + val)

/-- The `n`-th term of the sequence with seed `a(1) = c` (1-indexed). -/
def seq (c n : ℕ) : ℕ :=
  (state c n).1

theorem main :
    ∀ c : ℕ, 1 ≤ c → ∃ N v : ℕ, ∀ n : ℕ, N ≤ n → seq c n = v := by
  sorry

end OMA.S_oeis_a094405
