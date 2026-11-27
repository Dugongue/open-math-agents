import Mathlib

/-!
# OEIS A066888: primes between consecutive triangular numbers

Source: https://oeis.org/A066888
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of primes `p` with `T(n) < p ≤ T(n+1)`, `T(n) = n(n+1)/2`. It is conjectured
that `a(n) > 0` for `n > 0`.
-/

namespace OMA.S_oeis_a066888

/-- For every `n ≥ 1` there is a prime in `(T(n), T(n+1)]`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ p : ℕ, p.Prime ∧ n * (n + 1) / 2 < p ∧ p ≤ (n + 1) * (n + 2) / 2 := by
  sorry

end OMA.S_oeis_a066888
