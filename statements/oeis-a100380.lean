import Mathlib

/-!
# A100380: a(n) = least k such that prime(n) + A002110(k) is prime.

Source: https://oeis.org/A100380
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture: every prime number can be written as `+- p(n) -+ p(k)#` where `p(i)` is the
`i`-th prime and `p(i)#` is the `i`-th primorial.
-/

namespace OMA.S_oeis_a100380

/-- The `k`-th primorial `p(k)# = ∏_{i < k} p_i` (OEIS A002110). -/
noncomputable def primorial (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

theorem main :
    ∀ p : ℕ, Nat.Prime p →
      ∃ q k : ℕ, Nat.Prime q ∧
        ((p : ℤ) = (q : ℤ) - (primorial k : ℤ) ∨
         (p : ℤ) = (primorial k : ℤ) - (q : ℤ)) := by
  sorry

end OMA.S_oeis_a100380
