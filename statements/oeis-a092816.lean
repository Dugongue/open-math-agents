import Mathlib

/-!
# A092816: Number of Sophie Germain primes less than 10^n.

Source: https://oeis.org/A092816
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Hardy-Littlewood conjecture: Number of Sophie Germain primes less than n ~ 2*C2*n/(log(n))^2,
where C2 = 0.6601618158... is the twin prime constant (see A005597).
-/

namespace OMA.S_oeis_a092816

noncomputable def twinPrimeConst : ℝ :=
  ∏' p : {p : ℕ // Nat.Prime p ∧ 2 < p}, (1 - 1 / ((p.1 : ℝ) - 1) ^ 2)

def sgCount (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun p => Nat.Prime p ∧ Nat.Prime (2 * p + 1))).card

theorem main :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => (sgCount n : ℝ))
      (fun n : ℕ => 2 * twinPrimeConst * (n : ℝ) / (Real.log (n : ℝ)) ^ 2) := by
  sorry

end OMA.S_oeis_a092816
