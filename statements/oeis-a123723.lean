import Mathlib

/-!
# OEIS A123723: few squares modulo `n`

Source: https://oeis.org/A123723
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A123723 lists the `n` for which the number of squares modulo `n` (A000224) equals
`⌈(n+1)/4⌉`. Conjecture (OEIS entry): if `n > 4` is such a value and a multiple of `4`, then `n/4`
is prime.

Conventions:
* The number of squares mod `n` is the number of distinct values `x²` for `x ∈ ZMod n`;
  `⌈(n+1)/4⌉ = (n + 4)/4` in integer division. `n ≥ 1`.
-/

namespace OMA.S_oeis_a123723

/-- Number of squares modulo `n` (for `n ≥ 1`). -/
noncomputable def sq (n : ℕ) : ℕ := (Set.range fun x : ZMod n => x ^ 2).ncard

/-- For `n > 4`, `4 ∣ n` and `sq n = ⌈(n+1)/4⌉`, the number `n/4` is prime. -/
theorem main : ∀ n : ℕ, 4 < n → 4 ∣ n → sq n = (n + 4) / 4 → (n / 4).Prime := by
  sorry

end OMA.S_oeis_a123723
