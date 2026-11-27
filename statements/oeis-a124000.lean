import Mathlib

/-!
# OEIS A124000: semiprime binomial coefficients

Source: https://oeis.org/A124000
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A124000 lists the semiprimes among the binomial coefficients `C(n, k)`, `2 ≤ k ≤ n - 2`.
Conjectures (OEIS entry): all of them except `6` and `10` are odd; and all of them except `35` are
triangular numbers.

Conventions:
* Semiprime: `Ω = 2`. Triangular: `m(m+1)/2` for some `m`.
-/

namespace OMA.S_oeis_a124000

open ArithmeticFunction

/-- Both conjectures, for every semiprime `C(n, k)` with `2 ≤ k ≤ n - 2`. -/
theorem main : ∀ n k : ℕ, 2 ≤ k → k + 2 ≤ n → cardFactors (n.choose k) = 2 →
    (n.choose k = 6 ∨ n.choose k = 10 ∨ Odd (n.choose k)) ∧
    (n.choose k = 35 ∨ ∃ m : ℕ, n.choose k = m * (m + 1) / 2) := by
  sorry

end OMA.S_oeis_a124000
