import Mathlib

/-!
# A094802: a(n) = smallest k such that all of 1 through n divides k!.

Source: https://oeis.org/A094802
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

It is conjectured that after n=4 the sequence is prime for n prime or the
previous prime for n not prime.
-/

namespace OMA.S_oeis_a094802

/-- Smallest `k` such that every `m ∈ {1, ..., n}` divides `k!`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ m ∈ Finset.Icc 1 n, m ∣ Nat.factorial k}

theorem main :
    ∀ n : ℕ, 4 < n →
      (a n).Prime ∧ a n ≤ n ∧ ∀ p : ℕ, p.Prime → p ≤ n → p ≤ a n := by
  sorry

end OMA.S_oeis_a094802
