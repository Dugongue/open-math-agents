import Mathlib

/-!
# Is graph isomorphism in P?

Source: https://en.wikipedia.org/wiki/Graph_isomorphism_problem
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question: can it be decided in polynomial time whether two finite graphs are isomorphic?
`main` states the answer yes.

Conventions:
* A decision problem is a predicate `L : ℕ → Bool` on binary-encoded naturals; polynomial time is
  Mathlib's `Turing.TM2ComputableInPolyTime` with `Computability.finEncodingNatBool`, as in the
  `P vs. BPP` statement of this repository.
* Instances: `n = ⟨k, ⟨g, h⟩⟩` (`Nat.pair`) encodes two graphs on `Fin k`; for `i < j` the pair
  `{i, j}` is an edge of the first graph iff bit `i k + j` of `g` is set (likewise `h`). Every
  `n` decodes to an instance and decoding is polynomial-time, and pairs of graphs of different
  orders are trivially non-isomorphic, so this is the usual problem up to polynomial-time
  reductions in both directions.
-/

namespace OMA.S_wpc_graph_isomorphism_in_p

open Computability

/-- `L ∈ P`. -/
def InP (L : ℕ → Bool) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime encodingNatBool.encode encodingBoolBool.encode L)

/-- The graph on `Fin k` coded by the bits of `g`. -/
def decode (k g : ℕ) : SimpleGraph (Fin k) :=
  SimpleGraph.fromRel fun i j => g.testBit (min i.val j.val * k + max i.val j.val) = true

/-- The graph isomorphism problem on encoded instances. -/
def GI (n : ℕ) : Prop :=
  Nonempty (decode n.unpair.1 n.unpair.2.unpair.1 ≃g decode n.unpair.1 n.unpair.2.unpair.2)

/-- Graph isomorphism is decidable in polynomial time. -/
theorem main : InP (fun n => @decide (GI n) (Classical.dec _)) := by
  sorry

end OMA.S_wpc_graph_isomorphism_in_p
