import Mathlib

/-!
# Conway's thrackle conjecture

Source: https://en.wikipedia.org/wiki/Conway%27s_thrackle_conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Conway): every thrackle has at most as many edges as vertices.

Conventions:
* Graphs are finite simple graphs on `Fin n`; each edge `{u, v}` is listed once as `(u, v)`
  with `u < v`.
* A thrackle drawing places the vertices at distinct points of the plane and draws each edge as a
  smooth arc `γ : [0, 1] → ℝ²` (continuously differentiable, injective, nowhere-vanishing
  derivative) from `u` to `v` whose interior avoids every vertex, such that every two distinct
  edges meet exactly once: edges sharing an endpoint meet only there (their interiors are
  disjoint), and edges without a common endpoint have interiors meeting in exactly one point,
  where they cross transversally (linearly independent tangent vectors). Restricting to smooth
  drawings is the usual convention and loses no generality.
-/

namespace OMA.S_wp_conway_s_thrackle_conjecture_that_thrackles_cannot_have_more_edges_than_vertices

/-- The plane. -/
abbrev P2 := EuclideanSpace ℝ (Fin 2)

open Classical in
/-- The edges of `G`, each listed once as `(u, v)` with `u < v`. -/
noncomputable def edges {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun e => e.1 < e.2 ∧ G.Adj e.1 e.2

/-- Two listed edges share an endpoint. -/
def Adjacent {n : ℕ} (e f : Fin n × Fin n) : Prop :=
  e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2

/-- A thrackle drawing of `G`. -/
structure Thrackle {n : ℕ} (G : SimpleGraph (Fin n)) where
  pos : Fin n → P2
  arc : Fin n × Fin n → ℝ → P2
  pos_inj : Function.Injective pos
  arc_smooth : ∀ e ∈ edges G, ContDiff ℝ 1 (arc e)
  arc_deriv : ∀ e ∈ edges G, ∀ t ∈ Set.Icc (0 : ℝ) 1, deriv (arc e) t ≠ 0
  arc_inj : ∀ e ∈ edges G, Set.InjOn (arc e) (Set.Icc 0 1)
  arc_zero : ∀ e ∈ edges G, arc e 0 = pos e.1
  arc_one : ∀ e ∈ edges G, arc e 1 = pos e.2
  arc_avoid : ∀ e ∈ edges G, ∀ t ∈ Set.Ioo (0 : ℝ) 1, arc e t ∉ Set.range pos
  adjacent_meet : ∀ e ∈ edges G, ∀ f ∈ edges G, e ≠ f → Adjacent e f →
    Disjoint (arc e '' Set.Ioo 0 1) (arc f '' Set.Ioo 0 1)
  cross_once : ∀ e ∈ edges G, ∀ f ∈ edges G, ¬ Adjacent e f →
    ∃ s ∈ Set.Ioo (0 : ℝ) 1, ∃ t ∈ Set.Ioo (0 : ℝ) 1, arc e s = arc f t ∧
      LinearIndependent ℝ ![deriv (arc e) s, deriv (arc f) t] ∧
      ∀ s' ∈ Set.Ioo (0 : ℝ) 1, ∀ t' ∈ Set.Ioo (0 : ℝ) 1, arc e s' = arc f t' → s' = s ∧ t' = t

theorem main :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), Nonempty (Thrackle G) → (edges G).card ≤ n := by
  sorry

end OMA.S_wp_conway_s_thrackle_conjecture_that_thrackles_cannot_have_more_edges_than_vertices
