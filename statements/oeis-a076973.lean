import Mathlib

/-!
A076973: Starting with 2, largest prime divisor of the sum of all previous terms.

Source: https://oeis.org/A076973
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: start from any initial value a(1) = m >= 2 and define a(n) to be the largest prime factor of a(1)+a(2)+...+a(n-1); then a(n) = n/2 + O(log(n)) and there are infinitely many primes p such that a(2p)=p.
-/

namespace OMA.S_oeis_a076973

/-- Largest prime factor of `k` (or 0 if none). -/
noncomputable def largestPrimeFactor (k : ℕ) : ℕ :=
  sSup {p : ℕ | Nat.Prime p ∧ p ∣ k}

/-- Sequence starting at `a(1) = m` with `a(n)` the largest prime factor of `a(1) + ... + a(n - 1)`. -/
noncomputable def seq (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => m
  | n + 2 => largestPrimeFactor (∑ k : Fin (n + 1), seq m (k.1 + 1))

/-- Conjecture: for every `m ≥ 2`, `seq m n = n / 2 + O(log n)` and there are infinitely many
primes `p` such that `seq m (2 * p) = p`. -/
theorem main :
    ∀ m : ℕ, 2 ≤ m →
      (∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → |(seq m n : ℝ) - (n : ℝ) / 2| ≤ C * Real.log (n : ℝ)) ∧
      {p : ℕ | Nat.Prime p ∧ seq m (2 * p) = p}.Infinite := by sorry

end OMA.S_oeis_a076973
