import Mathlib

/-!
# OEIS A069180: `F(n)` coprime to `n!`

Source: https://oeis.org/A069180
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A069180 lists the `n` such that the Fibonacci number `F(n)` and `n!` are relatively prime.
Conjecture (OEIS entry): `a(n) = C n log n + o(n log n)` with `0.6 < C < 0.7`.

Conventions:
* `a(n) = Nat.nth P (n - 1)` (offset `1`); `o` is `IsLittleO` as `n → ∞`.
-/

namespace OMA.S_oeis_a069180

open Filter Asymptotics

/-- `gcd(F(n), n!) = 1`. -/
def P (n : ℕ) : Prop := Nat.Coprime (Nat.fib n) n.factorial

/-- `a(n) = C n log n + o(n log n)` with `0.6 < C < 0.7`. -/
theorem main : ∃ C : ℝ, 0.6 < C ∧ C < 0.7 ∧
    (fun n : ℕ => (Nat.nth P (n - 1) : ℝ) - C * n * Real.log n) =o[atTop]
      fun n => (n : ℝ) * Real.log n := by
  sorry

end OMA.S_oeis_a069180
