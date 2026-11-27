import Mathlib

/-!
# OEIS A076825: `u(n) = 2^u(n-1) mod n` returning to `1`

Source: https://oeis.org/A076825
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `u(1) = 1` and `u(n) = 2^u(n-1) mod n`; A076825 lists the `n` with `u(n) = 1`. Conjecture
(OEIS entry): `a(n)/n² → ∞`.

Conventions:
* `u 0` is a placeholder. `a(n) = Nat.nth P (n - 1)`; `a(n)/n² → ∞` is `Tendsto … atTop atTop`
  (which presupposes infinitely many terms).
-/

namespace OMA.S_oeis_a076825

open Filter

/-- `u(n)`. -/
def u : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 ^ u (n + 1) % (n + 2)

/-- `u(n) = 1`. -/
def P (n : ℕ) : Prop := 1 ≤ n ∧ u n = 1

/-- `a(n)/n² → ∞`. -/
theorem main : Tendsto (fun n : ℕ => (Nat.nth P (n - 1) : ℝ) / (n : ℝ) ^ 2) atTop atTop := by
  sorry

end OMA.S_oeis_a076825
