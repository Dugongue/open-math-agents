import Mathlib

/-!
# A098520: E.g.f. exp(x) * BesselI(1, 4*x) / 2

Source: https://oeis.org/A098520
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

E.g.f.: exp(x) * BesselI(1, 4*x) / 2.
Conjecture: (n-1)*(n+1)*a(n) - n*(2*n-1)*a(n-1) - 15*n*(n-1)*a(n-2) = 0.
-/

namespace OMA.S_oeis_a098520

def a (n : ℕ) : ℚ :=
  (n.factorial : ℚ) *
    ∑ k ∈ Finset.range (n / 2 + 1),
      if 2 * k + 1 ≤ n then
        (4 : ℚ) ^ k /
          ((k.factorial : ℚ) * ((k + 1).factorial : ℚ) * ((n - 2 * k - 1).factorial : ℚ))
      else
        0

theorem main :
    ∀ n : ℕ, 2 ≤ n →
      ((n : ℚ) - 1) * ((n : ℚ) + 1) * a n -
        (n : ℚ) * (2 * (n : ℚ) - 1) * a (n - 1) -
        15 * (n : ℚ) * ((n : ℚ) - 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a098520
