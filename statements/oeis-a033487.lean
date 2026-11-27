import Mathlib

/-!
# OEIS A033487: crossing numbers of cocktail party graphs

Source: https://oeis.org/A033487
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = n(n+1)(n+2)(n+3)/4`. The entry records the conjecture that `a(n)` is the crossing number
of the `(n+3)`-cocktail party graph.

Conventions:
* The `m`-cocktail party graph is `K_{2m}` minus a perfect matching: vertices `Fin m × Bool`, with
  `(i, s)` and `(j, t)` adjacent iff `i ≠ j`.
* A drawing places the vertices at distinct points of the plane and each edge as an arc (an
  injective path) between its endpoints whose interior avoids all vertices. Only drawings in which
  any two distinct edges meet in finitely many interior points are allowed, and `cr` minimises the
  number of (unordered pair of distinct edges, common interior point) incidences. This is the
  standard crossing number. `n ≥ 0`.
-/

namespace OMA.S_oeis_a033487

open Set

/-- The plane. -/
abbrev P := EuclideanSpace ℝ (Fin 2)

/-- A drawing of `G` in the plane, with an arc for each dart. -/
structure Drawing {V : Type} (G : SimpleGraph V) where
  pos : V → P
  pos_inj : Function.Injective pos
  arc : (d : G.Dart) → Path (pos d.fst) (pos d.snd)
  arc_inj : ∀ d, Function.Injective (arc d)
  arc_symm : ∀ d, arc d.symm = (arc d).symm
  arc_avoids : ∀ d (t : unitInterval), (t : ℝ) ∈ Ioo (0 : ℝ) 1 → arc d t ∉ range pos

variable {V : Type} {G : SimpleGraph V}

/-- The interior of the arc of an edge `e`. -/
def Drawing.inner (D : Drawing G) (e : Sym2 V) : Set P :=
  ⋃ (d : G.Dart) (_ : d.edge = e), (D.arc d) '' {t | (t : ℝ) ∈ Ioo (0 : ℝ) 1}

/-- Triples (edge, edge, point) of two distinct edges and a common interior point. -/
def Drawing.crossings (D : Drawing G) : Set (Sym2 V × Sym2 V × P) :=
  {p | p.1 ∈ G.edgeSet ∧ p.2.1 ∈ G.edgeSet ∧ p.1 ≠ p.2.1 ∧ p.2.2 ∈ D.inner p.1 ∩ D.inner p.2.1}

/-- Admissible drawings: every two distinct edges meet in finitely many interior points. -/
def Drawing.Good (D : Drawing G) : Prop := D.crossings.Finite

/-- The crossing number (each crossing is counted once for each order of its two edges,
hence the division by `2`). -/
noncomputable def cr (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ D : Drawing G, D.Good ∧ n = D.crossings.ncard / 2}

/-- The `m`-cocktail party graph. -/
def cocktail (m : ℕ) : SimpleGraph (Fin m × Bool) :=
  SimpleGraph.fromRel fun x y => x.1 ≠ y.1

/-- `cr(CP(n+3)) = n(n+1)(n+2)(n+3)/4`. -/
theorem main : ∀ n : ℕ, cr (cocktail (n + 3)) = n * (n + 1) * (n + 2) * (n + 3) / 4 := by
  sorry

end OMA.S_oeis_a033487
