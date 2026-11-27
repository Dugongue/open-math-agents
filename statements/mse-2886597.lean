import Mathlib

/-!
# Odd perfect numbers: does `D(n²)` being a square force `k = 1`?

Source: https://math.stackexchange.com/questions/2886597
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `q^k n²` be an odd perfect number with special (Euler) prime `q` (`q ≡ k ≡ 1 (mod 4)`,
`gcd(q, n) = 1`). Broughan et al. show that if `σ(n²)/q^k` is a square then `k = 1`. Question: does
`D(n²) = 2n² - σ(n²)` being a square imply `k = 1`? `main` states the answer yes.

Conventions:
* `N` is an odd perfect number when it is odd and `σ(N) = 2N`. The Euler form is
  `N = q^k n²` with `q` prime, `q ≡ k ≡ 1 (mod 4)` and `q ∤ n`. `D(n²)` is an integer.
-/

namespace OMA.S_mse_2886597

open ArithmeticFunction

/-- If `q^k n²` is an odd perfect number in Euler form and `2n² - σ(n²)` is a square, then
`k = 1`. -/
theorem main : ∀ q k n : ℕ, q.Prime → q % 4 = 1 → k % 4 = 1 → ¬ q ∣ n →
    Odd (q ^ k * n ^ 2) → ArithmeticFunction.sigma 1 (q ^ k * n ^ 2) = 2 * (q ^ k * n ^ 2) →
    IsSquare (2 * (n ^ 2 : ℤ) - ArithmeticFunction.sigma 1 (n ^ 2)) → k = 1 := by
  sorry

end OMA.S_mse_2886597
