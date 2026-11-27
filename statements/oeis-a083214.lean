import Mathlib

/-!
# OEIS A083214: partition numbers divisible by `3`

Source: https://oeis.org/A083214
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A083214 lists the `k` with `3 ∣ p(k)`, `p` the partition function. Conjecture (OEIS entry):
`a(n) = 3n + o(n)`.

Conventions:
* `p(k)` is the number of partitions of `k` (`Fintype.card (Nat.Partition k)`); `a(n) = Nat.nth P
  (n - 1)`; `o` is `IsLittleO` as `n → ∞`.
-/

namespace OMA.S_oeis_a083214

open Filter Asymptotics

/-- `3 ∣ p(k)`. -/
def P (k : ℕ) : Prop := 3 ∣ Fintype.card (Nat.Partition k)

/-- `a(n) = 3n + o(n)`. -/
theorem main : (fun n : ℕ => (Nat.nth P (n - 1) : ℝ) - 3 * n) =o[atTop] fun n => (n : ℝ) := by
  sorry

end OMA.S_oeis_a083214
