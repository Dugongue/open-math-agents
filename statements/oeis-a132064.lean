import Mathlib

/-!
# OEIS A132064: numbers reversed by multiplication by `4`

Source: https://oeis.org/A132064
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A132064 lists the numbers `n` such that `4n` is `n` written backwards (`0, 2178, 21978, …`).
Conjecture (OEIS entry): `a(n)^(1/n) → 10`.

Conventions:
* 'Written backwards' is reversal of the decimal digits (`Nat.ofDigits` of the reversed digit
  list). Terms are enumerated by `Nat.nth` from index `0` (`a 0 = 0`); the index shift does not
  affect the limit.
-/

namespace OMA.S_oeis_a132064

open Filter Topology

/-- Decimal reversal. -/
def rev (m : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 m).reverse

/-- `4n` is the reversal of `n`. -/
def P (n : ℕ) : Prop := 4 * n = rev n

/-- `a(n)^(1/n) → 10`. -/
theorem main : Tendsto (fun n : ℕ => (Nat.nth P n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 10) := by
  sorry

end OMA.S_oeis_a132064
