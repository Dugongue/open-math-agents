import Mathlib

/-!
# OEIS A065376: primes of the form `p + k²`

Source: https://oeis.org/A065376
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A065376 lists the primes of the form `p + k²` with `p` prime and `k > 0`. Conjecture (OEIS
entry): it contains all primes `> 7549`.
-/

namespace OMA.S_oeis_a065376

/-- Every prime `q > 7549` is `p + k²` with `p` prime and `k ≥ 1`. -/
theorem main : ∀ q : ℕ, q.Prime → 7549 < q → ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ q = p + k ^ 2 := by
  sorry

end OMA.S_oeis_a065376
