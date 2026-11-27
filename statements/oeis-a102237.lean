import Mathlib

/-!
# OEIS A102237: products of `n` primes that are sums of `n` distinct primes

Source: https://oeis.org/A102237
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the smallest number equal to the product of `n` primes which is also the sum of `n`
distinct primes. Conjecture (OEIS entry): `a(n) = 2ⁿ` for `n > 5`.

Conventions:
* 'Product of `n` primes' counts primes with multiplicity (`Ω(m) = n`).
-/

namespace OMA.S_oeis_a102237

open ArithmeticFunction

/-- `m` is a product of `n` primes and a sum of `n` distinct primes. -/
def P (n m : ℕ) : Prop :=
  cardFactors m = n ∧ ∃ s : Finset ℕ, s.card = n ∧ (∀ p ∈ s, p.Prime) ∧ ∑ p ∈ s, p = m

/-- For `n > 5`, the least such `m` is `2ⁿ`. -/
theorem main : ∀ n : ℕ, 5 < n → IsLeast {m | P n m} (2 ^ n) := by
  sorry

end OMA.S_oeis_a102237
