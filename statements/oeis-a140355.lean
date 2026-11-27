import Mathlib

/-!
# OEIS A140355: multiples with strictly increasing numbers of divisors

Source: https://oeis.org/A140355
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the smallest integer `k` such that the first `n` multiples `k, 2k, …, nk` have strictly
increasing numbers of divisors. Conjecture (OEIS entry): this sequence is finite, i.e. for all
large `n` no such `k` exists.
-/

namespace OMA.S_oeis_a140355

/-- `τ(k) < τ(2k) < ⋯ < τ(nk)`. -/
def Inc (n k : ℕ) : Prop := ∀ i, 1 ≤ i → i < n → (i * k).divisors.card < ((i + 1) * k).divisors.card

/-- For all large `n` there is no `k ≥ 1` with `Inc n k`. -/
theorem main : ∃ N : ℕ, ∀ n ≥ N, ¬ ∃ k : ℕ, 1 ≤ k ∧ Inc n k := by
  sorry

end OMA.S_oeis_a140355
