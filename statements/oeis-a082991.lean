import Mathlib

/-!
# OEIS A082991: alternating `σ` and `φ` is ultimately periodic

Source: https://oeis.org/A082991
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

For `n ≥ 1` define `u(1) = n`, `u(2k) = σ(u(2k-1))`, `u(2k+1) = φ(u(2k))`. A082991 records the
length of the ultimate period, and the sequence `u` is conjectured to become ultimately periodic
for every `n ≥ 1`; `main` states this.

Conventions:
* Equivalently, the iteration of `x ↦ φ(σ(x))` from `n` is ultimately periodic, i.e. its orbit
  is finite; `main` states that there are `i < j` with equal iterates.
-/

namespace OMA.S_oeis_a082991

open ArithmeticFunction

/-- `x ↦ φ(σ(x))`. -/
def g (x : ℕ) : ℕ := Nat.totient (ArithmeticFunction.sigma 1 x)

/-- For every `n ≥ 1` the orbit of `n` under `g` is ultimately periodic. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ i j : ℕ, i < j ∧ g^[i] n = g^[j] n := by
  sorry

end OMA.S_oeis_a082991
