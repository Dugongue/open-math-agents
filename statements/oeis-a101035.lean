import Mathlib

/-!
# A101035: Dirichlet inverse of the gcd-sum function (A018804).

Source: https://oeis.org/A101035
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: The logarithmic generating function of the Dirichlet inverse `a` of the gcd-sum
function `g(n) = ∑_{k=1}^n gcd(k, n)` is
`∑_{n>0, k>0} μ(n) * μ(k) * log(1 / (1 - x^(n * k)))`.
-/

namespace OMA.S_oeis_a101035

/-- Pillai's gcd-sum function `g(n) = ∑_{k=1}^n gcd(k, n)` (OEIS A018804) as an
arithmetic function. -/
def gcdSum : ArithmeticFunction ℤ where
  toFun n := if n = 0 then 0 else ∑ k ∈ Finset.Icc 1 n, (Nat.gcd k n : ℤ)
  map_zero' := by simp

theorem main :
    ∃ a : ArithmeticFunction ℤ, a * gcdSum = 1 ∧
      ∀ x : ℝ, |x| < 1 →
        (∑' m : ℕ+, (a m : ℝ) * x ^ (m : ℕ) / (m : ℝ)) =
          ∑' n : ℕ+, ∑' k : ℕ+,
            (ArithmeticFunction.moebius n : ℝ) * (ArithmeticFunction.moebius k : ℝ) *
              Real.log (1 / (1 - x ^ ((n : ℕ) * (k : ℕ)))) := by
  sorry

end OMA.S_oeis_a101035
