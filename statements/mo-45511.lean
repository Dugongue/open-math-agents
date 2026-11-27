import Mathlib

/-!
# Density of values of polynomials in two variables

Source: https://mathoverflow.net/questions/45511
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `f ∈ ℚ[x, y]` with `f(ℤ × ℤ) ⊆ ℕ`, and let `g(n)` be the number of elements of
`f(ℤ × ℤ) ∩ {0, 1, …, n}`. Is it always true that `g(n) = O(n / √(log n))`? (Best possible:
`x² + y²` gives `g(n) ~ c n / √(log n)`.)

Conventions:
* Polynomials in two variables are `MvPolynomial (Fin 2) ℚ`; `f(ℤ × ℤ) ⊆ ℕ` means every value at
  an integer point is a natural number.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_mo_45511

open Classical

open Asymptotics Filter

/-- The value of `f` at the integer point `(x, y)`. -/
noncomputable def val (f : MvPolynomial (Fin 2) ℚ) (x y : ℤ) : ℚ :=
  MvPolynomial.eval ![(x : ℚ), (y : ℚ)] f

/-- `g(n) = #(f(ℤ × ℤ) ∩ {0, …, n})`. -/
noncomputable def g (f : MvPolynomial (Fin 2) ℚ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun m => ∃ x y : ℤ, val f x y = (m : ℚ)).card

/-- `g(n) = O(n / √(log n))` for every such `f`. -/
theorem main : ∀ f : MvPolynomial (Fin 2) ℚ, (∀ x y : ℤ, ∃ m : ℕ, val f x y = m) →
    (fun n : ℕ => (g f n : ℝ)) =O[atTop] (fun n => (n : ℝ) / Real.sqrt (Real.log n)) := by
  sorry

end OMA.S_mo_45511
