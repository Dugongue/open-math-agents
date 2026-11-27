import Mathlib

/-!
# OEIS A062368: a triple inverse Möbius transform

Source: https://oeis.org/A062368
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A062368 is multiplicative with `a(p^e) = (e+1)(e+2)(4e+3)/6`. Conjecture (OEIS entry): it is the
third inverse Möbius transform of `n ↦ 4^ω(n)` (`ω` = number of distinct prime factors).

Conventions:
* The inverse Möbius transform of `f` is `ζ * f` (Dirichlet convolution with the constant `1`);
  the third one is `ζ * ζ * ζ * f`, in Mathlib's `ArithmeticFunction ℕ`.
* `a(n) = ∏_{p^e ∥ n} (e+1)(e+2)(4e+3)/6`, computed from `Nat.factorization` (each factor is an
  integer).
-/

namespace OMA.S_oeis_a062368

open ArithmeticFunction

/-- `n ↦ 4^ω(n)`. -/
def f : ArithmeticFunction ℕ := ⟨fun n => if n = 0 then 0 else 4 ^ n.primeFactors.card, by simp⟩

/-- A062368 at `n ≥ 1`. -/
def a (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors,
    (n.factorization p + 1) * (n.factorization p + 2) * (4 * n.factorization p + 3) / 6

/-- `a = ζ * ζ * ζ * 4^ω` on positive integers. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = ((ζ : ArithmeticFunction ℕ) * ζ * ζ * f) n := by
  sorry

end OMA.S_oeis_a062368
