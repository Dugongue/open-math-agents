import Mathlib

/-!
# OEIS A122379: `n² < P(n)!` for almost all `n`

Source: https://oeis.org/A122379
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

With `P(n)` the greatest prime factor of `n`, the entry records the conjecture that `n² < P(n)!`
for almost all `n`.

Conventions:
* 'Almost all' means asymptotic density `1`: `#{n ≤ N | n² < P(n)!}/N → 1`. `P(n)` is the
  largest element of `n.primeFactors` (`0` for `n = 1`).
-/

namespace OMA.S_oeis_a122379

open Filter Topology

/-- The greatest prime factor. -/
def P (n : ℕ) : ℕ := n.primeFactors.sup id

/-- `n² < P(n)!` on a set of density `1`. -/
theorem main : Tendsto (fun N : ℕ =>
    (((Finset.Icc 1 N).filter fun n => n ^ 2 < (P n).factorial).card : ℝ) / N) atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a122379
