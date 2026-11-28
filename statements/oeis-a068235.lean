import Mathlib

/-!
# OEIS A068235: n consecutive primes all ≡ 11 (mod 12)

Source: https://oeis.org/A068235
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the smallest prime `p` such that `p` and the next `n - 1` primes are all `≡ 11 (mod 12)`.
The entry notes that Dickson's conjecture implies `a(n)` exists for all `n`; `main` states this
existence for every `n ≥ 1` (runs of `n` consecutive primes, `pᵢ, …, p_{i+n-1}`).
-/

namespace OMA.S_oeis_a068235

/-- For every `n ≥ 1` there are `n` consecutive primes all congruent to `11` mod `12`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ i : ℕ, ∀ j < n, Nat.nth Nat.Prime (i + j) % 12 = 11 := by
  sorry

end OMA.S_oeis_a068235
