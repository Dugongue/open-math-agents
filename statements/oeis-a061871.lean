import Mathlib

/-!
# OEIS A061871: alternating digit sum `±2`

Source: https://oeis.org/A061871
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A061871 lists the numbers whose alternating digit sum `|d₁ - d₂ + d₃ - d₄ + ⋯|` is `2`
(`d₁` the leading digit). Conjecture (OEIS entry): `a(n) ~ k n √(log n)` for some `k`.

Conventions:
* The absolute value of the alternating sum does not depend on whether one starts from the
  leading or the last digit, so it is computed from `Nat.digits 10` (least significant first).
  `a(n) = Nat.nth P (n - 1)`; `k > 0` is implicit in `~`.
-/

namespace OMA.S_oeis_a061871

open Filter Asymptotics

/-- Alternating sum of a digit list (first entry with sign `+`). -/
def alt : List ℕ → ℤ
  | [] => 0
  | d :: ds => d - alt ds

/-- `|alternating digit sum of m| = 2`. -/
def P (m : ℕ) : Prop := |alt (Nat.digits 10 m)| = 2

/-- `a(n) ~ k n √(log n)` for some `k > 0`. -/
theorem main : ∃ k : ℝ, 0 < k ∧ IsEquivalent atTop (fun n : ℕ => (Nat.nth P (n - 1) : ℝ))
    (fun n => k * n * Real.sqrt (Real.log n)) := by
  sorry

end OMA.S_oeis_a061871
