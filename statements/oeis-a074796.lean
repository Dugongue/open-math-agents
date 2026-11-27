import Mathlib

/-!
# OEIS A074796: density of `τ(k) ≡ 2 (mod 3)`

Source: https://oeis.org/A074796
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of `k ≤ n` with `τ(k) ≡ 2 (mod 3)` (`τ` = number of divisors). The entry
records that `a(n)/n` tends to a constant, conjecturally `3ζ(3)/π² = 0.36538…`.

Conventions:
* `ζ(3) = ∑_{m ≥ 1} 1/m³` (Mathlib's `riemannZeta 3`, real part). `main` states
  `a(n)/n → 3ζ(3)/π²`.
-/

namespace OMA.S_oeis_a074796

open Filter Topology

/-- `a(n) = #{1 ≤ k ≤ n | τ(k) ≡ 2 (mod 3)}`. -/
def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter fun k => k.divisors.card % 3 = 2).card

/-- `a(n)/n → 3ζ(3)/π²`. -/
theorem main : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop
    (𝓝 (3 * (riemannZeta 3).re / Real.pi ^ 2)) := by
  sorry

end OMA.S_oeis_a074796
