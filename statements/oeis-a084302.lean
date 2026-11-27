import Mathlib

/-!
# OEIS A084302: mean of `τ(n) mod 6`

Source: https://oeis.org/A084302
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = τ(n) mod 6`. Conjecture (OEIS entry): the asymptotic mean of this sequence is
`3 ζ(3)/ζ(2) = 2.192288…`.

Conventions:
* `ζ(3)` is `(riemannZeta 3).re` and `ζ(2) = π²/6`.
-/

namespace OMA.S_oeis_a084302

open Filter Topology

/-- `(1/n) ∑_{k ≤ n} (τ(k) mod 6) → 3ζ(3)/ζ(2)`. -/
theorem main : Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, ((k.divisors.card % 6 : ℕ) : ℝ)) / n)
    atTop (𝓝 (3 * (riemannZeta 3).re / (Real.pi ^ 2 / 6))) := by
  sorry

end OMA.S_oeis_a084302
