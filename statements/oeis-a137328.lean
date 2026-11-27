import Mathlib

/-!
# OEIS A137328: primes minus the largest primorial below them

Source: https://oeis.org/A137328
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = prime(n) - primorial(k)`, where `k` is the greatest number with `primorial(k) ≤ prime(n)`.
Conjecture (OEIS entry): each prime number appears in this sequence at least once.

Conventions:
* `primorial(k) = prime(1) ⋯ prime(k)` (`primorial(0) = 1`), and the subtracted value is the
  largest primorial `≤ prime(n)`.
-/

namespace OMA.S_oeis_a137328

/-- The `k`-th primorial. -/
noncomputable def primorial (k : ℕ) : ℕ := ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

/-- `a` at the prime `q`: `q` minus the largest primorial `≤ q`. -/
noncomputable def a (q : ℕ) : ℕ := q - sSup {t : ℕ | ∃ k, t = primorial k ∧ t ≤ q}

/-- Every prime `r` equals `a(q)` for some prime `q`. -/
theorem main : ∀ r : ℕ, r.Prime → ∃ q : ℕ, q.Prime ∧ a q = r := by
  sorry

end OMA.S_oeis_a137328
