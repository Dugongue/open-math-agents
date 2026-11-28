import Mathlib

/-!
# Do Siegel zeros exist?

Source: https://en.wikipedia.org/wiki/Siegel_zero
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question: do Siegel (Landau–Siegel) zeros exist? The expected answer (implied by GRH) is no;
`main` states it: there is `c > 0` such that for every modulus `q` and every primitive real
(quadratic) Dirichlet character `χ` mod `q`, `L(s, χ)` has no real zero `β` with
`1 - c / log q < β < 1`. A proof of its negation shows that Siegel zeros exist.

Conventions: a real non-principal character is one with `χ ≠ 1` and `χ ^ 2 = 1`; `L(s, χ)` is
Mathlib's `DirichletCharacter.LFunction` (the analytic continuation of the L-series).
-/

namespace OMA.S_wp_do_siegel_zeros_exist

theorem main :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 →
      ∀ β : ℝ, 1 - c / Real.log q < β → β < 1 → DirichletCharacter.LFunction χ β ≠ 0 := by
  sorry

end OMA.S_wp_do_siegel_zeros_exist
