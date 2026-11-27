import Mathlib

/-!
# OEIS A072611: `φ(k) ∣ σ(k+1) - σ(k)`, growth exponent

Source: https://oeis.org/A072611
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A072611 lists the `k` with `φ(k) ∣ σ(k+1) - σ(k)`. Conjecture (OEIS entry):
`lim_{n → ∞} log(a(n))/log(n)` exists and equals `2.6…`.

Conventions:
* The difference `σ(k+1) - σ(k)` is an integer (possibly negative). `a(n) = Nat.nth P (n - 1)`;
  `2.6…` is read as `[2.6, 2.7)`.
-/

namespace OMA.S_oeis_a072611

open Filter Topology ArithmeticFunction

/-- `φ(k) ∣ σ(k+1) - σ(k)`. -/
def P (k : ℕ) : Prop := 1 ≤ k ∧ (Nat.totient k : ℤ) ∣ (ArithmeticFunction.sigma 1 (k + 1) : ℤ) - ArithmeticFunction.sigma 1 k

/-- `log a(n)/log n → L ∈ [2.6, 2.7)`. -/
theorem main : ∃ L : ℝ, 2.6 ≤ L ∧ L < 2.7 ∧
    Tendsto (fun n : ℕ => Real.log (Nat.nth P (n - 1)) / Real.log n) atTop (𝓝 L) := by
  sorry

end OMA.S_oeis_a072611
