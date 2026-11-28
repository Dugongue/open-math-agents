import Mathlib

/-!
# A298368: Zarankiewicz's conjecture for the crossing number of K_{k,n}

Source: https://oeis.org/A298368
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A298368: Triangle read by rows:
T(n, k) = floor((n-1)/2)*floor(n/2)*floor((k-1)/2)*floor(k/2).

Statement:
T(n, k) is conjectured by Zarankiewicz's conjecture to be the crossing number of the complete
bipartite graph K_{k,n}.

Conventions:
- We model drawings of `K_{k,n}` as piecewise-linear drawings in `ℝ^2` with distinct vertex
  positions, simple polygonal arcs for edges not passing through non-incident vertices, and
  finitely many interior intersection points between any two distinct edges.
- The crossing count of a drawing is the sum over unordered pairs of distinct edges of the
  number of interior intersection points between them.
-/

namespace OMA.S_oeis_a298368

/-- Zarankiewicz's formula `T(n, k)`. -/
def zarankiewicz (n k : ℕ) : ℕ :=
  ((n - 1) / 2) * (n / 2) * ((k - 1) / 2) * (k / 2)

/-- Closed line segment between two points in `ℝ^2`. -/
def closedSeg (p q : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {x | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = ((1 - t) * p.1 + t * q.1, (1 - t) * p.2 + t * q.2)}

/-- The point set of a polygonal path given by a list of vertices. -/
def polyTrace : List (ℝ × ℝ) → Set (ℝ × ℝ)
  | [] => ∅
  | [_] => ∅
  | p :: q :: rest => closedSeg p q ∪ polyTrace (q :: rest)

/-- The interior of a polygonal arc (excluding its two endpoints `u` and `v`). -/
def arcInterior (u v : ℝ × ℝ) (pts : List (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  polyTrace pts \ {u, v}

/-- A piecewise-linear drawing of the complete bipartite graph `K_{k,n}` in `ℝ^2`. -/
structure BipartiteDrawing (k n : ℕ) where
  posL : Fin k → ℝ × ℝ
  posR : Fin n → ℝ × ℝ
  posL_inj : Function.Injective posL
  posR_inj : Function.Injective posR
  disjoint_parts : ∀ i j, posL i ≠ posR j
  edge : Fin k → Fin n → List (ℝ × ℝ)
  edge_head : ∀ i j, (edge i j).head? = some (posL i)
  edge_last : ∀ i j, (edge i j).getLast? = some (posR j)
  no_vertex_in_interior :
    ∀ i j, (∀ i', posL i' ∉ arcInterior (posL i) (posR j) (edge i j)) ∧
           (∀ j', posR j' ∉ arcInterior (posL i) (posR j) (edge i j))
  finite_crossings :
    ∀ e₁ e₂ : Fin k × Fin n, e₁ ≠ e₂ →
      (arcInterior (posL e₁.1) (posR e₁.2) (edge e₁.1 e₁.2) ∩
       arcInterior (posL e₂.1) (posR e₂.2) (edge e₂.1 e₂.2)).Finite

/-- Total number of pairwise interior crossings in a drawing of `K_{k,n}`. -/
noncomputable def crossingCount {k n : ℕ} (D : BipartiteDrawing k n) : ℕ :=
  (∑ e₁ : Fin k × Fin n, ∑ e₂ : Fin k × Fin n,
    if e₁ = e₂ then 0
    else (arcInterior (D.posL e₁.1) (D.posR e₁.2) (D.edge e₁.1 e₁.2) ∩
          arcInterior (D.posL e₂.1) (D.posR e₂.2) (D.edge e₂.1 e₂.2)).ncard) / 2

theorem main :
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      (∀ D : BipartiteDrawing k n, zarankiewicz n k ≤ crossingCount D) ∧
      (∃ D : BipartiteDrawing k n, crossingCount D = zarankiewicz n k) := by
  sorry

end OMA.S_oeis_a298368
