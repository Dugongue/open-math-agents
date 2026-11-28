import Mathlib

/-!
# Models omitting countably many types: from `ℵ_{ω₁}` to the continuum

Source: https://en.wikipedia.org/wiki/Type_(model_theory)
(listed in https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics, citing
Shelah, Borel sets with large squares, Fund. Math. 159 (1999)).

Question: let `K` be the class of models of a countable first-order theory omitting countably
many types. If `K` has a model of cardinality `ℵ_{ω₁}`, does it have a model of cardinality
continuum? We state the affirmative answer.

Conventions.
- The language is countable (`L.card ≤ ℵ₀`); models live in `Type`.
- A type is a (partial) type: a set of formulas in finitely many free variables `Fin n`.
  A structure omits it if no tuple satisfies all of its formulas.
- The countably many types are indexed by a countable type `ι`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_wp_types

open FirstOrder

/-- `M` omits every type in the family `p`. -/
def OmitsAll {L : FirstOrder.Language.{0, 0}} (M : Type) [L.Structure M] {ι : Type} (n : ι → ℕ)
    (p : ∀ i, Set (L.Formula (Fin (n i)))) : Prop :=
  ∀ i (v : Fin (n i) → M), ∃ φ ∈ p i, ¬ φ.Realize v

theorem main :
    ∀ (L : FirstOrder.Language.{0, 0}), L.card ≤ Cardinal.aleph0 →
      ∀ (T : L.Theory) (ι : Type) [Countable ι] (n : ι → ℕ)
        (p : ∀ i, Set (L.Formula (Fin (n i)))),
        (∃ (M : Type) (_ : L.Structure M), M ⊨ T ∧ OmitsAll M n p ∧
            Cardinal.mk M = Cardinal.aleph (Ordinal.omega 1)) →
        ∃ (N : Type) (_ : L.Structure N), N ⊨ T ∧ OmitsAll N n p ∧
            Cardinal.mk N = Cardinal.continuum := by
  sorry

end OMA.S_wp_types
