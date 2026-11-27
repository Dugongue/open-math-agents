import Mathlib

/-!
# OEIS A074636: the recursion `b(k+1) = b(k) - ⌊k/b(k)⌋` always reaches `0`

Source: https://oeis.org/A074636
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Define `b(1) = n` and `b(k+1) = b(k) - ⌊k/b(k)⌋`; `a(n)` is the index with `b(a(n)) = 0`.
Conjecture (OEIS entry): `a(n)` is always defined, i.e. the sequence `b` reaches `0`.

Conventions:
* `n ≥ 1`; `b` is computed in `ℤ` with floor division (`Int.fdiv`); after reaching `0` the
  recursion would divide by `0`, but only reaching `0` matters.
-/

namespace OMA.S_oeis_a074636

/-- `b(k)` for start `n` (indexed so that `b n 1 = n`; `b n 0` is a placeholder). -/
def b (n : ℕ) : ℕ → ℤ
  | 0 => n
  | 1 => n
  | k + 2 => b n (k + 1) - Int.fdiv (k + 1) (b n (k + 1))

/-- For every `n ≥ 1` the sequence `b` reaches `0`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ b n k = 0 := by
  sorry

end OMA.S_oeis_a074636
