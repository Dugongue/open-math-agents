import Mathlib

/-!
# A098660: E.g.f. BesselI(0, 2*sqrt(2)*x) + BesselI(1, 2*sqrt(2)*x) / sqrt(2)

Source: https://oeis.org/A098660
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

E.g.f.: BesselI(0, 2*sqrt(2)*x) + BesselI(1, 2*sqrt(2)*x) / sqrt(2).
Conjecture: (n+1)*a(n) + (n-1)*a(n-1) - n*a(n-2) + (2-n)*a(n-3) = 0.
-/

namespace OMA.S_oeis_a098660

def a (n : ℕ) : ℚ :=
  if n % 2 = 0 then
    ((n.factorial : ℚ) * (2 : ℚ) ^ (n / 2)) / (((n / 2).factorial : ℚ) ^ 2)
  else
    ((n.factorial : ℚ) * (2 : ℚ) ^ (n / 2)) /
      (((n / 2).factorial : ℚ) * ((n / 2 + 1).factorial : ℚ))

theorem main :
    ∀ n : ℕ, 3 ≤ n →
      ((n : ℚ) + 1) * a n + ((n : ℚ) - 1) * a (n - 1) -
        (n : ℚ) * a (n - 2) + (2 - (n : ℚ)) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a098660
