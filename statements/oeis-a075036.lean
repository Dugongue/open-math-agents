import Mathlib

/-!
A075036: Smaller of two smallest consecutive numbers with 2n divisors.

Source: https://oeis.org/A075036
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: if a term k is even, the highest p-adic order of k (the maximum may be attained by several p's) occurs at p=2 and the highest p-adic order of k+1 occurs at p=3. If a term k is odd, the highest p-adic order of k occurs at p=3 and the highest p-adic order of k+1 occurs at p=2.
-/

namespace OMA.S_oeis_a075036

/-- Smaller of the two smallest consecutive positive integers each having `2 * n` divisors. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ k.divisors.card = 2 * n ∧ (k + 1).divisors.card = 2 * n}

/-- The highest `p`-adic valuation of `m` is attained at prime `q`. -/
def HasMaxPadicOrder (m q : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → m.factorization p ≤ m.factorization q

/-- Conjecture: if `a(n)` is even, then `a(n)` attains its maximum `p`-adic order at `p = 2` and
`a(n) + 1` at `p = 3`; if `a(n)` is odd, then `a(n)` attains it at `p = 3` and `a(n) + 1` at `p = 2`. -/
theorem main :
    ∀ n : ℕ, 0 < n →
      (Even (a n) → HasMaxPadicOrder (a n) 2 ∧ HasMaxPadicOrder (a n + 1) 3) ∧
      (Odd (a n) → HasMaxPadicOrder (a n) 3 ∧ HasMaxPadicOrder (a n + 1) 2) := by sorry

end OMA.S_oeis_a075036
