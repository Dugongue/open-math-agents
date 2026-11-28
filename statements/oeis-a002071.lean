import Mathlib

/-!
# A002071: Conditional Values of Smooth Consecutive Integer Pairs under Effective ABC

Source: https://oeis.org/A002071
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

A002071(n) is the number of pairs of consecutive positive integers `(x, x + 1)` such that all
prime factors of both `x` and `x + 1` are at most the `n`-th prime `p_n`.

Conjecture/Conditional claim: Assuming the effective abc conjecture `c < rad(a * b * c)^2` for
all coprime positive integers `a + b = c`, the values of `A002071(n)` for `n = 20, ..., 36` are
`(4839, 6040, 7441, 9179, 11134, 13374, 16167, 19507, 23367, 27949, 33233, 39283, 46166, 54150,
63428, 74007, 86125)`.
-/

namespace OMA.S_oeis_a002071

/-- The radical of a positive integer: product of its distinct prime factors. -/
def rad (m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors, p

/-- The effective abc conjecture `c < rad(a * b * c)^2`. -/
def EffectiveABC : Prop :=
  ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c → c < (rad (a * b * c)) ^ 2

/-- Number of positive integers `x` such that every prime dividing `x * (x + 1)` is at most the
`n`-th prime (`1`-indexed, so `n = 1` gives `p_1 = 2`). -/
noncomputable def smoothConsecCount (n : ℕ) : ℕ :=
  Set.ncard { x : ℕ | 0 < x ∧ ∀ p : ℕ, Nat.Prime p → p ∣ x * (x + 1) →
    p ≤ Nat.nth Nat.Prime (n - 1) }

theorem main :
    EffectiveABC →
      smoothConsecCount 20 = 4839 ∧
      smoothConsecCount 21 = 6040 ∧
      smoothConsecCount 22 = 7441 ∧
      smoothConsecCount 23 = 9179 ∧
      smoothConsecCount 24 = 11134 ∧
      smoothConsecCount 25 = 13374 ∧
      smoothConsecCount 26 = 16167 ∧
      smoothConsecCount 27 = 19507 ∧
      smoothConsecCount 28 = 23367 ∧
      smoothConsecCount 29 = 27949 ∧
      smoothConsecCount 30 = 33233 ∧
      smoothConsecCount 31 = 39283 ∧
      smoothConsecCount 32 = 46166 ∧
      smoothConsecCount 33 = 54150 ∧
      smoothConsecCount 34 = 63428 ∧
      smoothConsecCount 35 = 74007 ∧
      smoothConsecCount 36 = 86125 := by
  sorry

end OMA.S_oeis_a002071
