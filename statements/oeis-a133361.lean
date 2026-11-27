import Mathlib

/-!
# OEIS A133361: numbers reversed by multiplication by `9`

Source: https://oeis.org/A133361
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A133361 lists the numbers `n` such that `9n` is `n` written backwards (`0, 1089, 10989, …`).
Conjecture (OEIS entry): `a(n)^(1/n) → 10`.

Conventions:
* 'Written backwards' is reversal of the decimal digits. Terms are enumerated by `Nat.nth` from
  index `0`; the index shift does not affect the limit.
-/

namespace OMA.S_oeis_a133361

open Filter Topology

/-- Decimal reversal. -/
def rev (m : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 m).reverse

/-- `9n` is the reversal of `n`. -/
def P (n : ℕ) : Prop := 9 * n = rev n

/-- `a(n)^(1/n) → 10`. -/
theorem main : Tendsto (fun n : ℕ => (Nat.nth P n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 10) := by
  sorry

end OMA.S_oeis_a133361
