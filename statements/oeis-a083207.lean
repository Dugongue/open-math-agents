import Mathlib

/-!
# OEIS A083207: Zumkeller numbers

Source: https://oeis.org/A083207
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A Zumkeller number is a positive integer whose divisors can be partitioned into two disjoint
sets with equal sums. Conjectures (OEIS entry): (1) any 12 consecutive numbers include a
Zumkeller number; (2) any 4 consecutive Zumkeller numbers include one, `k`, with `σ(k)/2` also
Zumkeller; (3) if `d > 1`, `d ∣ k` and `τ(d) σ(d) = k`, then `k` is a Zumkeller number.

Conventions:
* '12 consecutive numbers' are `m, m+1, …, m+11` with `m ≥ 1`. '4 consecutive terms' are the
  `i`-th to `(i+3)`-th Zumkeller numbers (`Nat.nth`, indexed from `0`); for Zumkeller `k`,
  `σ(k)` is even. `τ` and `σ` are `σ 0` and `σ 1`.
-/

namespace OMA.S_oeis_a083207

open ArithmeticFunction

/-- `k` is a Zumkeller number. -/
def IsZumkeller (k : ℕ) : Prop :=
  0 < k ∧ ∃ S ⊆ k.divisors, ∑ d ∈ S, d = ∑ d ∈ k.divisors \ S, d

/-- Conjectures (1), (2) and (3). -/
theorem main :
    (∀ m : ℕ, 1 ≤ m → ∃ j < 12, IsZumkeller (m + j)) ∧
    (∀ i : ℕ, ∃ j < 4, IsZumkeller (ArithmeticFunction.sigma 1 (Nat.nth IsZumkeller (i + j)) / 2)) ∧
    (∀ d k : ℕ, 1 < d → d ∣ k → ArithmeticFunction.sigma 0 d * ArithmeticFunction.sigma 1 d = k → IsZumkeller k) := by
  sorry

end OMA.S_oeis_a083207
