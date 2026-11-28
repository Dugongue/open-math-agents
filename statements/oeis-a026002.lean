import Mathlib

/-!
# A026002: Delannoy diagonal T(n, n + 2) and array m(i, j)

Source: https://oeis.org/A026002
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture: Let `D(n, k)` be the Delannoy numbers (`D(0, k) = D(n, 0) = 1`,
`D(n + 1, k + 1) = D(n + 1, k) + D(n, k) + D(n, k + 1)`), and let `m(i, j)` (`i, j ≥ 1`)
be defined by `m(n, 1) = m(1, n) = n * (n - 1) + 1` and
`m(i + 1, j + 1) = m(i + 1, j) + m(i, j) + m(i, j + 1)`.
Then `m(n + 1, n + 1) = D(n, n + 2)` for all `n ≥ 0`.
-/

namespace OMA.S_oeis_a026002

/-- The Delannoy array `D(n, k)` (`n, k ≥ 0`). -/
def delannoy : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 1
  | n + 1, k + 1 => delannoy (n + 1) k + delannoy n k + delannoy n (k + 1)

/-- The array `m(i, j)` (shifted to 0-indexed `m0 i j = m (i + 1) (j + 1)`). -/
def m0 : ℕ → ℕ → ℕ
  | 0, j => (j + 1) * j + 1
  | i + 1, 0 => (i + 2) * (i + 1) + 1
  | i + 1, j + 1 => m0 (i + 1) j + m0 i j + m0 i (j + 1)

theorem main :
    ∀ n : ℕ, m0 n n = delannoy n (n + 2) := by
  sorry

end OMA.S_oeis_a026002
