import Mathlib

/-!
# OEIS A064709: runs of consecutive numbers with exactly two distinct prime factors

Source: https://oeis.org/A064709
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the initial term of the first run of exactly `n` consecutive numbers each having exactly
two distinct prime factors. The terms up to `a(8) = 141` are the only ones below `10^18`.
Conjecture (OEIS entry): `141` is the last term, i.e. there is no run of `9` (or more) consecutive
numbers each with exactly two distinct prime factors.

Conventions:
* `ω(m) = m.primeFactors.card`. A run of exactly `n ≥ 9` contains a run of `9`, so `main` states
  that no `9` consecutive integers all have `ω = 2`.
-/

namespace OMA.S_oeis_a064709

/-- No `9` consecutive positive integers all have exactly two distinct prime factors. -/
theorem main : ∀ m : ℕ, ¬ ∀ j < 9, (m + j).primeFactors.card = 2 := by
  sorry

end OMA.S_oeis_a064709
