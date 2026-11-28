import Mathlib

/-!
# Mazur's conjecture on the topology of rational points

Source: https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics
(entry "Mazur's conjectures", citing B. Mazur, *The topology of rational points*, Experiment.
Math. 1 (1992))
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Mazur, 1992): for a smooth variety `V` over `ℚ`, the closure of `V(ℚ)` in `V(ℝ)` has
only finitely many connected components.

Conventions. We state it for affine `ℚ`-varieties given by finitely many polynomials
`S ⊆ ℚ[x₁, …, xₙ]`: the set of rational solutions, viewed in `ℝⁿ`, has a closure with finitely
many connected components. This is equivalent to Mazur's statement: a smooth variety is covered by
finitely many affine opens, and conversely for an arbitrary affine variety one inducts on the
dimension, splitting off the (lower-dimensional) singular locus, since taking closures can only
merge components.
-/

namespace OMA.S_wp_mazur_s_conjectures

/-- The rational points of the affine variety `{S = 0}`, as a subset of `ℝⁿ`. -/
def ratPoints {n : ℕ} (S : Finset (MvPolynomial (Fin n) ℚ)) : Set (Fin n → ℝ) :=
  {x | ∃ q : Fin n → ℚ, x = (fun i => (q i : ℝ)) ∧ ∀ f ∈ S, MvPolynomial.eval q f = 0}

theorem main :
    ∀ (n : ℕ) (S : Finset (MvPolynomial (Fin n) ℚ)),
      Finite (ConnectedComponents (closure (ratPoints S))) := by
  sorry

end OMA.S_wp_mazur_s_conjectures
