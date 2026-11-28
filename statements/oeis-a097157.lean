import Mathlib

/-!
# A097157: Fixed points of f(x) = reverse(x) - maxdigit(x)

Source: https://oeis.org/A097157
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Number of iterations of f(x) = reverse(x) - maxdigit(x) needed for the numbers in A097155
to reach 89.
It is conjectured that 0 and 89 are the only fixed points of f.
-/

namespace OMA.S_oeis_a097157

def reverseDigits (x : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 x).reverse

def maxDigit (x : ℕ) : ℕ :=
  (Nat.digits 10 x).foldl max 0

def f (x : ℕ) : ℕ :=
  reverseDigits x - maxDigit x

theorem main :
    ∀ x : ℕ, f x = x ↔ x = 0 ∨ x = 89 := by
  sorry

end OMA.S_oeis_a097157
