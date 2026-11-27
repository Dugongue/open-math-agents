import Mathlib

/-!
# OEIS A089381: the map `m ↦ m/2` or `m + rev(m)` always cycles

Source: https://oeis.org/A089381
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `P(m) = m/2` if `m` is even and `P(m) = m + rev(m)` if `m` is odd (`rev` = decimal reversal).
It is conjectured (OEIS entry) that every number eventually cycles when `P` is applied
repeatedly.

Conventions:
* `k ≥ 1`. Eventually cycling means two iterates coincide.
-/

namespace OMA.S_oeis_a089381

/-- Decimal digit reversal. -/
def rev (m : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 m).reverse

/-- The map `P`. -/
def P (m : ℕ) : ℕ := if m % 2 = 0 then m / 2 else m + rev m

/-- Every orbit is ultimately periodic. -/
theorem main : ∀ k : ℕ, 1 ≤ k → ∃ i j : ℕ, i < j ∧ P^[i] k = P^[j] k := by
  sorry

end OMA.S_oeis_a089381
