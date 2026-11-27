import Mathlib

/-!
# OEIS A109864: least palindromic prime beginning with `n`

Source: https://oeis.org/A109864
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the least palindromic prime beginning with `n` (in decimal), or `0` if none exists.
Conjecture (OEIS entry): `a(n) = 0` iff `n > 3` and the leading digit of `n` is `2, 4, 5, 6` or
`8`.

Conventions:
* `p` begins with `n` when the decimal digits of `n` are an initial segment of those of `p`; with
  Mathlib's least-significant-first `Nat.digits`, that is `Nat.digits 10 n <:+ Nat.digits 10 p`.
  The leading digit of `n ≥ 1` is the last entry of `Nat.digits 10 n`. `n ≥ 1`.
-/

namespace OMA.S_oeis_a109864

/-- Decimal palindrome. -/
def IsPal (m : ℕ) : Prop := (Nat.digits 10 m).reverse = Nat.digits 10 m

/-- No palindromic prime begins with `n` iff `n > 3` and its leading digit is in
`{2, 4, 5, 6, 8}`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ((¬ ∃ p : ℕ, p.Prime ∧ IsPal p ∧ Nat.digits 10 n <:+ Nat.digits 10 p) ↔
      (3 < n ∧ (Nat.digits 10 n).getLast? ∈ ({some 2, some 4, some 5, some 6, some 8} : Set (Option ℕ)))) := by
  sorry

end OMA.S_oeis_a109864
