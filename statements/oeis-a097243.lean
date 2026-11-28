import Mathlib

/-!
# A097243: Expansion of 1 + 32 * (eta(q^4) / eta(q))^8 in powers of q

Source: https://oeis.org/A097243
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Expansion of 1 + 32 * (eta(q^4) / eta(q))^8 = 1 + 32 * q * Prod_{n>=1} ((1 + q^n)*(1 + q^(2*n)))^8
in powers of q.
Conjecture: Sum_{k>=0} a(k) / exp(k*Pi) = 3.
-/

namespace OMA.S_oeis_a097243

noncomputable def polyTrunc (k : ℕ) : Polynomial ℤ :=
  1 + 32 * Polynomial.X *
    ∏ n ∈ Finset.Icc 1 k, ((1 + Polynomial.X ^ n) * (1 + Polynomial.X ^ (2 * n))) ^ 8

noncomputable def a (k : ℕ) : ℤ :=
  (polyTrunc k).coeff k

theorem main :
    HasSum (fun k : ℕ => (a k : ℝ) / Real.exp ((k : ℝ) * Real.pi)) 3 := by
  sorry

end OMA.S_oeis_a097243
