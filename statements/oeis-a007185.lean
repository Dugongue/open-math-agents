import Mathlib

/-!
# A007185: Automorphic numbers ending in digit 5

Source: https://oeis.org/A007185
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture:
Let `a(n) = 5^(2^n) mod 10^n`. For any positive integer `m` coprime to `10` and any
integer `k`, the natural density of `n` such that `a(n) ≡ k (mod m)` is `1 / m`.
-/

namespace OMA.S_oeis_a007185

/-- A007185: `a(n) = 5^(2^n) mod 10^n`. -/
def a (n : ℕ) : ℕ :=
  5 ^ (2 ^ n) % 10 ^ n

/-- For every `m > 0` coprime to `10` and every `k`, the natural density of
`{n : ℕ | a(n) ≡ k (mod m)}` is `1 / m`. -/
theorem main :
    ∀ m k : ℕ, 0 < m → Nat.Coprime m 10 →
      Filter.Tendsto
        (fun N : ℕ => (((Finset.range N).filter (fun n => a n % m = k % m)).card : ℝ) / (N : ℝ))
        Filter.atTop (nhds (1 / (m : ℝ))) := by
  sorry

end OMA.S_oeis_a007185
