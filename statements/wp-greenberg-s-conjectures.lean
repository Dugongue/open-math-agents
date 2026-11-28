import Mathlib

/-!
# Greenberg's conjecture

Source: https://en.wikipedia.org/wiki/Greenberg%27s_conjectures
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Greenberg, 1976): for a totally real number field `K` and a prime `p`, the Iwasawa
invariants `μ` and `λ` of the cyclotomic `ℤ_p`-extension of `K` vanish; equivalently, the
`p`-parts of the class numbers of its layers `K_n` stay bounded as `n → ∞`.

Conventions:
* Number fields are intermediate fields of `ℚ̄ = AlgebraicClosure ℚ`. `K` is a finite extension
  of `ℚ` all of whose complex embeddings are real.
* The `n`-th layer of the cyclotomic `ℤ_p`-extension of `ℚ` is the unique totally real subfield
  `ℚ_n` of degree `p^n` of `ℚ(μ_{p^{n+2}})` (for odd `p` it is the degree-`p^n` subfield of
  `ℚ(μ_{p^{n+1}})`; for `p = 2` it is the maximal real subfield of `ℚ(μ_{2^{n+2}})`). The `n`-th
  layer of the cyclotomic `ℤ_p`-extension of `K` is the compositum `K_n = K ℚ_n`.
* The class number of `K_n` is the cardinality of the class group of its ring of integers, and
  its `p`-part is measured by `padicValNat p`.
-/

namespace OMA.S_wp_greenberg_s_conjectures

/-- `ℚ̄`. -/
abbrev Qbar := AlgebraicClosure ℚ

/-- `ℚ(μ_m)` inside `ℚ̄`. -/
noncomputable def cyclo (m : ℕ) : IntermediateField ℚ Qbar :=
  IntermediateField.adjoin ℚ {x : Qbar | x ^ m = 1}

/-- Every complex embedding of `F` is real. -/
def TotallyReal (F : IntermediateField ℚ Qbar) : Prop :=
  ∀ (φ : F →+* ℂ) (x : F), (φ x).im = 0

theorem main :
    ∀ (p : ℕ), p.Prime → ∀ K : IntermediateField ℚ Qbar, FiniteDimensional ℚ K →
      TotallyReal K →
      ∃ C : ℕ, ∀ (n : ℕ) (F : IntermediateField ℚ Qbar),
        F ≤ cyclo (p ^ (n + 2)) → Module.finrank ℚ F = p ^ n → TotallyReal F →
          padicValNat p (Nat.card (ClassGroup (NumberField.RingOfIntegers ↥(K ⊔ F)))) ≤ C := by
  sorry

end OMA.S_wp_greenberg_s_conjectures
