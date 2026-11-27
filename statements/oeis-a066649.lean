import Mathlib

/-!
# OEIS A066649: primes of the form `a² + b³`

Source: https://oeis.org/A066649
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A066649 lists the primes `a² + b³` with `a, b > 0`. The entry notes that on Merikoski's
Conjecture `C_a(1/17)` this sequence is infinite and `a(n) ≪ n^(6/5) log n`; `main` states these
two consequences.

Conventions:
* `a(n) = Nat.nth P (n - 1)` (offset `1`); `≪` is `IsBigO` as `n → ∞`.
-/

namespace OMA.S_oeis_a066649

open Filter Asymptotics

/-- `q` is a prime of the form `a² + b³`, `a, b ≥ 1`. -/
def P (q : ℕ) : Prop := q.Prime ∧ ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ q = a ^ 2 + b ^ 3

/-- Infinitely many such primes, and `a(n) = O(n^(6/5) log n)`. -/
theorem main : {q | P q}.Infinite ∧
    (fun n : ℕ => (Nat.nth P (n - 1) : ℝ)) =O[atTop] fun n => (n : ℝ) ^ ((6 : ℝ) / 5) * Real.log n := by
  sorry

end OMA.S_oeis_a066649
