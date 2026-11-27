import Mathlib

/-!
# OEIS A083371: Cloitre's largest-prime-factor recursion

Source: https://oeis.org/A083371
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

From the original definition by Cloitre: start from any initial value `F(1) ≥ 2` and let `F(n)` be
the largest prime factor of `F(1) + F(2) + ⋯ + F(n-1)`. Conjecture: `F(n) = n/2 + O(log n)`.
(The entry's other conjecture, that the resulting sequence of primes is infinite, concerns the
current definition, primes followed by a gap of at least `8`; `main` states the growth
conjecture for every start.)

Conventions:
* Indexing from `0` (`F 0 = F(1)`); the sums are `≥ 2`, so the largest prime factor
  (`primeFactors.sup id`) is defined.
-/

namespace OMA.S_oeis_a083371

open Filter Asymptotics

/-- `(F(n), F(1) + ⋯ + F(n))` from the start `s`. -/
def step (s : ℕ) : ℕ → ℕ × ℕ
  | 0 => (s, s)
  | n + 1 => let t := (step s n).2; let f := t.primeFactors.sup id; (f, t + f)

/-- `F(n)` for the start `s`. -/
def F (s n : ℕ) : ℕ := (step s n).1

/-- `F(n) - n/2 = O(log n)` for every start `s ≥ 2`. -/
theorem main : ∀ s : ℕ, 2 ≤ s →
    (fun n : ℕ => (F s n : ℝ) - n / 2) =O[atTop] fun n => Real.log n := by
  sorry

end OMA.S_oeis_a083371
