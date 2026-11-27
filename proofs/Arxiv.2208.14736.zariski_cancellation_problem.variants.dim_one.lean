import FormalConjectures.Arxiv.«2208.14736».ZariskiCancellation
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Proof of Zariski Cancellation in Dimension One (`Arxiv.«2208.14736».zariski_cancellation_problem.variants.dim_one`)

For any field `k` (in any characteristic) and any `k`-algebra `B` with `k[X][Y] ≃ₐ[k] B[Y]`,
we prove `k[X] ≃ₐ[k] B` via Abhyankar–Eakin–Heinzer's elementary method.
-/

-- Problem: Zariski Cancellation — dim one
-- Upstream: formal-conjectures FormalConjectures/Arxiv/2208.14736/ZariskiCancellation.lean:80 (declaration Arxiv.«2208.14736».zariski_cancellation_problem.variants.dim_one)
-- Credit: @Dugongue (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Polynomial

namespace OMA.ZariskiDimOne

universe u v

private lemma isDomain_of_poly_equiv {k : Type u} [Field k] {B : Type v} [CommRing B] [Algebra k B]
    (e : k[X][X] ≃ₐ[k] B[X]) : IsDomain B := by
  have : IsDomain B[X] := e.symm.injective.isDomain e.symm.toRingHom
  exact Polynomial.C_injective.isDomain (Polynomial.C : B →+* B[X])

private lemma isIntegrallyClosed_of_poly_equiv {k : Type u} [Field k] {B : Type v}
    [CommRing B] [Algebra k B] [IsDomain B] (e : k[X][X] ≃ₐ[k] B[X]) :
    IsIntegrallyClosed B := by
  let ι : B →+* k[X][X] := e.symm.toRingHom.comp Polynomial.C
  have hι_inj : Function.Injective ι := e.symm.injective.comp Polynomial.C_injective
  let L := FractionRing k[X][X]
  have : IsIntegrallyClosed k[X][X] := inferInstance
  have hj_inj : Function.Injective ((algebraMap k[X][X] L).comp ι) :=
    (IsFractionRing.injective k[X][X] L).comp hι_inj
  let j : FractionRing B →+* L := IsFractionRing.lift hj_inj
  have hj_map : ∀ b : B, j (algebraMap B (FractionRing B) b) = algebraMap k[X][X] L (ι b) :=
    fun b => IsFractionRing.lift_algebraMap hj_inj b
  rw [isIntegrallyClosed_iff (FractionRing B)]
  intro x hx
  obtain ⟨P, hP_monic, hPx⟩ := hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := B) x
  have hPι_monic : (P.map ι).Monic := hP_monic.map ι
  have hPι_eval : Polynomial.aeval (j (algebraMap B (FractionRing B) a /
      algebraMap B (FractionRing B) b)) (P.map ι) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hcomp : (algebraMap k[X][X] L).comp ι = j.comp (algebraMap B (FractionRing B)) := by
      ext r
      exact (hj_map r).symm
    rw [hcomp, ← Polynomial.hom_eval₂]
    simpa [Polynomial.aeval_def] using congrArg j hPx
  have hint_y : IsIntegral k[X][X] (j (algebraMap B (FractionRing B) a /
      algebraMap B (FractionRing B) b)) := ⟨P.map ι, hPι_monic, hPι_eval⟩
  obtain ⟨w, hw⟩ := (isIntegrallyClosed_iff L).mp inferInstance hint_y
  have hwb_L : algebraMap k[X][X] L (w * ι b) = algebraMap k[X][X] L (ι a) := by
    rw [map_mul, hw, ← hj_map, ← map_mul, div_mul_cancel₀ _ (by
      intro h0
      exact nonZeroDivisors.ne_zero hb ((IsFractionRing.injective B (FractionRing B))
        (by simpa using h0))), hj_map]
  have hwb : w * ι b = ι a := IsFractionRing.injective k[X][X] L hwb_L
  have hew : e w * C b = C a := by
    have := congrArg e hwb
    simpa [ι] using this
  have hcoeff := congrArg (fun p : B[X] => p.coeff 0) hew
  simp only [Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero] at hcoeff
  refine ⟨(e w).coeff 0, ?_⟩
  rw [eq_div_iff (by
    intro h0
    exact nonZeroDivisors.ne_zero hb ((IsFractionRing.injective B (FractionRing B))
      (by simpa using h0))), ← map_mul, hcoeff]

private lemma not_surjective_algebraMap_of_poly_equiv {k : Type u} [Field k] {B : Type v}
    [CommRing B] [Algebra k B] [IsDomain B] (e : k[X][X] ≃ₐ[k] B[X]) :
    ∃ b : B, b ∉ Set.range (algebraMap k B) := by
  by_contra h
  push Not at h
  have hbij : Function.Bijective (Algebra.ofId k B) :=
    ⟨RingHom.injective (algebraMap k B), h⟩
  let eB : k ≃ₐ[k] B := AlgEquiv.ofBijective (Algebra.ofId k B) hbij
  let φ : k[X][X] ≃+* k[X] := (e.trans (Polynomial.mapAlgEquiv eB.symm)).toRingEquiv
  let I : Ideal k[X][X] := Ideal.span {(C X : k[X][X]), X}
  let J : Ideal k[X] := I.map φ.toRingHom
  obtain ⟨g₀, hg₀⟩ := IsPrincipalIdealRing.principal J
  let g : k[X][X] := φ.symm g₀
  have hIg : I = Ideal.span {g} := by
    have h1 : I = J.map φ.symm.toRingHom := by
      simp [J, Ideal.map_map]
    rw [h1, hg₀, Ideal.map_span, Set.image_singleton]
    rfl
  have hCX : C X ∈ Ideal.span {g} := hIg ▸ Ideal.subset_span (by simp)
  have hX : (X : k[X][X]) ∈ Ideal.span {g} := hIg ▸ Ideal.subset_span (by simp)
  rw [Ideal.mem_span_singleton] at hCX hX
  have hCX_ne : (C X : k[X][X]) ≠ 0 := by simp
  have hg_deg : g.natDegree = 0 := by
    have hle := Polynomial.natDegree_le_of_dvd hCX hCX_ne
    simp at hle
    exact hle
  have hg_eq : g = C (g.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hg_deg
  obtain ⟨q, hq⟩ := hX
  rw [hg_eq] at hq
  have hq1 := congrArg (fun p : k[X][X] => p.coeff 1) hq
  simp only [Polynomial.coeff_X_one, Polynomial.coeff_C_mul] at hq1
  have hunit : IsUnit (g.coeff 0) := isUnit_iff_exists_inv.mpr ⟨q.coeff 1, hq1.symm⟩
  have h1_mem : (1 : k[X][X]) ∈ I := by
    rw [hIg, Ideal.mem_span_singleton, hg_eq]
    obtain ⟨u, hu⟩ := hunit
    refine ⟨C (u⁻¹ : k[X]ˣ), ?_⟩
    rw [← hu, ← map_mul]
    simp
  let ev : k[X][X] →+* k := (Polynomial.evalRingHom 0).comp (Polynomial.evalRingHom 0)
  have hev_zero : ∀ f ∈ I, ev f = 0 := by
    intro f hf
    refine Submodule.span_induction ?_ (by simp) (fun x y _ _ hx hy => by simp [hx, hy])
      (fun a x _ hx => by simp [hx]) hf
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp [ev]
  have h10 := hev_zero 1 h1_mem
  simp [ev] at h10

private lemma exists_algDep_in_poly {k : Type u} [Field k] (p q : k[X]) :
    ∃ (m : ℕ) (c : Fin (m + 1) × Fin (m + 1) → k),
      c ≠ 0 ∧ ∑ ij : Fin (m + 1) × Fin (m + 1), c ij • (p ^ ij.1.1 * q ^ ij.2.1) = 0 := by
  let D : ℕ := max p.natDegree q.natDegree + 1
  let m : ℕ := 2 * D + 1
  let N : ℕ := 2 * m * D + 1
  let T : (Fin (m + 1) × Fin (m + 1) → k) →ₗ[k] (Fin N → k) :=
    { toFun := fun c r =>
        (∑ ij : Fin (m + 1) × Fin (m + 1), c ij • (p ^ ij.1.1 * q ^ ij.2.1)).coeff r.1
      map_add' := fun c₁ c₂ => by
        ext r
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by
        ext r
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Polynomial.finsetSum_coeff,
          Polynomial.coeff_smul, Finset.mul_sum, mul_assoc] }
  have hnot_inj : ¬ Function.Injective T := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    simp only [Module.finrank_pi, Fintype.card_prod, Fintype.card_fin] at hle
    have hlt : N < (m + 1) * (m + 1) := by
      dsimp [N, m]
      nlinarith
    omega
  have hker : ∃ c, c ≠ 0 ∧ T c = 0 := by
    by_contra h
    push Not at h
    apply hnot_inj
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    by_contra hc0
    exact h c hc0 hc
  obtain ⟨c, hc0, hTc⟩ := hker
  refine ⟨m, c, hc0, ?_⟩
  ext r
  by_cases hr : r < N
  · have := congrFun hTc ⟨r, hr⟩
    simpa [T] using this
  · simp only [Polynomial.coeff_zero]
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun ij _ => ?_
    rw [Polynomial.coeff_smul]
    have hdeg : (p ^ ij.1.1 * q ^ ij.2.1).natDegree < N := by
      have hp : (p ^ ij.1.1).natDegree ≤ m * D := by
        calc (p ^ ij.1.1).natDegree ≤ ij.1.1 * p.natDegree := Polynomial.natDegree_pow_le
          _ ≤ m * D := Nat.mul_le_mul (Nat.le_of_lt_succ ij.1.2)
              (le_trans (le_max_left _ _) (Nat.le_succ _))
      have hq : (q ^ ij.2.1).natDegree ≤ m * D := by
        calc (q ^ ij.2.1).natDegree ≤ ij.2.1 * q.natDegree := Polynomial.natDegree_pow_le
          _ ≤ m * D := Nat.mul_le_mul (Nat.le_of_lt_succ ij.2.2)
              (le_trans (le_max_right _ _) (Nat.le_succ _))
      have hN : m * D + m * D < N := by
        dsimp [N]
        linarith
      exact lt_of_le_of_lt (le_trans Polynomial.natDegree_mul_le (add_le_add hp hq)) hN
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg (not_lt.mp hr)), smul_zero]

private lemma case_X_in_range {k : Type u} [Field k] {B : Type v}
    [CommRing B] [Algebra k B] [IsDomain B] (e : k[X][X] ≃ₐ[k] B[X])
    (b₀ : B) (hb₀ : e.symm (C b₀) = X) : Nonempty (k[X] ≃ₐ[k] B) := by
  let ev0 : k[X][X] →ₐ[k] k[X] := (Polynomial.aeval (R := k[X]) (0 : k[X])).restrictScalars k
  let π : B[X] →ₐ[k] k[X] := ev0.comp e.symm.toAlgHom
  let f₀ : B →ₐ[k] k[X] := π.comp (Polynomial.CAlgHom (R := k) (A := B))
  have hπ_dvd : ∀ P : B[X], π P = 0 ↔ C b₀ ∣ P := by
    intro P
    have h1 : π P = 0 ↔ X ∣ e.symm P := by
      change (e.symm P).eval 0 = 0 ↔ X ∣ e.symm P
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    rw [h1]
    constructor
    · rintro ⟨Q, hQ⟩
      refine ⟨e Q, ?_⟩
      apply e.symm.injective
      rw [map_mul, hb₀, e.symm_apply_apply, hQ]
    · rintro ⟨Q, rfl⟩
      exact ⟨e.symm Q, by rw [map_mul, hb₀]⟩
  have hf₀_dvd : ∀ b : B, f₀ b = 0 ↔ b₀ ∣ b := by
    intro b
    change π (C b) = 0 ↔ b₀ ∣ b
    rw [hπ_dvd]
    constructor
    · rintro ⟨Q, hQ⟩
      refine ⟨Q.coeff 0, ?_⟩
      have := congrArg (fun p : B[X] => p.coeff 0) hQ
      simpa using this
    · rintro ⟨c, rfl⟩
      exact ⟨C c, by rw [map_mul]⟩
  have hf₀_const : ∀ b : B, ∃ c : k, f₀ b = C c := by
    intro b
    by_contra hnc
    have hp_pos : 0 < (f₀ b).natDegree := by
      rcases Nat.eq_zero_or_pos (f₀ b).natDegree with h0 | hpos
      · exfalso
        exact hnc ⟨(f₀ b).coeff 0, Polynomial.eq_C_of_natDegree_eq_zero h0⟩
      · exact hpos
    obtain ⟨m, c, hc0, hsum⟩ := exists_algDep_in_poly (f₀ b) (π X)
    let P : B[X] := ∑ j : Fin (m + 1), C (∑ i : Fin (m + 1), c (i, j) • b ^ i.1) * X ^ j.1
    have hπP : π P = 0 := by
      have h1 : π P = ∑ j : Fin (m + 1),
          (∑ i : Fin (m + 1), c (i, j) • (f₀ b) ^ i.1) * (π X) ^ j.1 := by
        dsimp [P]
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, map_pow]
        congr 1
        change f₀ (∑ i : Fin (m + 1), c (i, j) • b ^ i.1) = _
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, map_pow]
      rw [h1]
      have h2 : ∑ j : Fin (m + 1), (∑ i : Fin (m + 1), c (i, j) • (f₀ b) ^ i.1) * (π X) ^ j.1 =
          ∑ ij : Fin (m + 1) × Fin (m + 1), c ij • ((f₀ b) ^ ij.1.1 * (π X) ^ ij.2.1) := by
        rw [Fintype.sum_prod_type_right]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_mul_assoc]
      rw [h2, hsum]
    obtain ⟨Q, hPQ⟩ := (hπ_dvd P).mp hπP
    have hcoeff_div : ∀ j : Fin (m + 1), b₀ ∣ ∑ i : Fin (m + 1), c (i, j) • b ^ i.1 := by
      intro j
      have hc := congrArg (fun p : B[X] => p.coeff j.1) hPQ
      rw [Polynomial.coeff_C_mul] at hc
      have hPc : P.coeff j.1 = ∑ i : Fin (m + 1), c (i, j) • b ^ i.1 := by
        dsimp [P]
        rw [Polynomial.finsetSum_coeff]
        rw [Finset.sum_eq_single j]
        · simp only [Polynomial.coeff_C_mul_X_pow, ↓reduceIte]
        · intro j' _ hne
          have hne_val : j.1 ≠ j'.1 := fun h => hne (Fin.ext h.symm)
          simp only [Polynomial.coeff_C_mul_X_pow, hne_val, ↓reduceIte]
        · intro hmem
          exact absurd (Finset.mem_univ j) hmem
      rw [hPc] at hc
      exact ⟨Q.coeff j.1, hc⟩
    have hex : ∃ ij : Fin (m + 1) × Fin (m + 1), c ij ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hc0 (funext hall)
    obtain ⟨⟨i₀, j₀⟩, hij₀⟩ := hex
    have hf₀_zero : f₀ (∑ i : Fin (m + 1), c (i, j₀) • b ^ i.1) = 0 :=
      (hf₀_dvd _).mpr (hcoeff_div j₀)
    let g : k[X] := ∑ i : Fin (m + 1), C (c (i, j₀)) * X ^ i.1
    have hg_ne : g ≠ 0 := by
      intro hg0
      have := congrArg (fun p : k[X] => p.coeff i₀.1) hg0
      rw [Polynomial.coeff_zero, Polynomial.finsetSum_coeff, Finset.sum_eq_single i₀] at this
      · simp only [Polynomial.coeff_C_mul_X_pow, ↓reduceIte] at this
        exact hij₀ this
      · intro i' _ hne
        have hne_val : i₀.1 ≠ i'.1 := fun h => hne (Fin.ext h.symm)
        simp only [Polynomial.coeff_C_mul_X_pow, hne_val, ↓reduceIte]
      · intro hmem
        exact absurd (Finset.mem_univ i₀) hmem
    have hg_comp : g.comp (f₀ b) = 0 := by
      dsimp [g]
      rw [Polynomial.sum_comp]
      have h3 : ∑ i : Fin (m + 1), (C (c (i, j₀)) * X ^ i.1).comp (f₀ b) =
          f₀ (∑ i : Fin (m + 1), c (i, j₀) • b ^ i.1) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp, map_smul, map_pow,
          Polynomial.smul_eq_C_mul]
      rw [h3, hf₀_zero]
    have hcomp_deg : (g.comp (f₀ b)).natDegree = g.natDegree * (f₀ b).natDegree :=
      Polynomial.natDegree_comp
    rw [hg_comp, Polynomial.natDegree_zero] at hcomp_deg
    have hg_deg0 : g.natDegree = 0 := by
      have := mul_eq_zero.mp hcomp_deg.symm
      exact this.resolve_right hp_pos.ne'
    have hg_C : g = C (g.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hg_deg0
    rw [hg_C, Polynomial.C_comp] at hg_comp
    exact hg_ne (hg_C.trans hg_comp)
  have hmem_adjoin : ∀ d : ℕ, ∀ b : B, (e.symm (C b)).natDegree ≤ d →
      b ∈ Algebra.adjoin k ({b₀} : Set B) := by
    intro d
    induction d with
    | zero =>
      intro b hdeg
      obtain ⟨c, hc⟩ := hf₀_const b
      have hdiv : b₀ ∣ b - algebraMap k B c := by
        rw [← hf₀_dvd, map_sub, hc, AlgHom.commutes]
        simp
      obtain ⟨b', hb'⟩ := hdiv
      have hb'0 : b' = 0 := by
        by_contra hne
        have he_ne : e.symm (C b') ≠ 0 := fun h0 =>
          hne (Polynomial.C_injective (e.symm.injective (by simpa using h0)))
        have hc_alg : e.symm (C (algebraMap k B c)) = C (C c) := by
          change e.symm (algebraMap k B[X] c) = algebraMap k k[X][X] c
          exact e.symm.commutes c
        have heq : e.symm (C b) - C (C c) = X * e.symm (C b') := by
          have := congrArg (fun r : B => e.symm (C r)) hb'
          simp only [map_sub, map_mul, hb₀, hc_alg] at this
          exact this
        have hdeg_rhs : (X * e.symm (C b')).natDegree = (e.symm (C b')).natDegree + 1 := by
          rw [Polynomial.natDegree_mul Polynomial.X_ne_zero he_ne, Polynomial.natDegree_X, add_comm]
        have hdeg_lhs : (e.symm (C b) - C (C c)).natDegree = 0 := by
          have hle : (e.symm (C b) - C (C c)).natDegree ≤ 0 := by
            refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
            simp [Nat.le_zero.mp hdeg]
          exact Nat.le_zero.mp hle
        rw [heq, hdeg_rhs] at hdeg_lhs
        omega
      rw [hb'0, mul_zero, sub_eq_zero] at hb'
      rw [hb']
      exact Subalgebra.algebraMap_mem _ c
    | succ d ih =>
      intro b hdeg
      obtain ⟨c, hc⟩ := hf₀_const b
      have hdiv : b₀ ∣ b - algebraMap k B c := by
        rw [← hf₀_dvd, map_sub, hc, AlgHom.commutes]
        simp
      obtain ⟨b', hb'⟩ := hdiv
      have hb_eq : b = algebraMap k B c + b₀ * b' := eq_add_of_sub_eq' hb'
      rcases eq_or_ne b' 0 with rfl | hne
      · rw [mul_zero, add_zero] at hb_eq
        rw [hb_eq]
        exact Subalgebra.algebraMap_mem _ c
      · have he_ne : e.symm (C b') ≠ 0 := fun h0 =>
          hne (Polynomial.C_injective (e.symm.injective (by simpa using h0)))
        have hc_alg : e.symm (C (algebraMap k B c)) = C (C c) := by
          change e.symm (algebraMap k B[X] c) = algebraMap k k[X][X] c
          exact e.symm.commutes c
        have heq : e.symm (C b) - C (C c) = X * e.symm (C b') := by
          have := congrArg (fun r : B => e.symm (C r)) hb'
          simp only [map_sub, map_mul, hb₀, hc_alg] at this
          exact this
        have hdeg_rhs : (X * e.symm (C b')).natDegree = (e.symm (C b')).natDegree + 1 := by
          rw [Polynomial.natDegree_mul Polynomial.X_ne_zero he_ne, Polynomial.natDegree_X, add_comm]
        have hdeg_lhs : (e.symm (C b) - C (C c)).natDegree ≤ d + 1 := by
          refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
          simp [hdeg]
        rw [heq, hdeg_rhs] at hdeg_lhs
        have hb'_deg : (e.symm (C b')).natDegree ≤ d := by omega
        rw [hb_eq]
        exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ c)
          (Subalgebra.mul_mem _ (Algebra.subset_adjoin rfl) (ih b' hb'_deg))
  have hsurj : Function.Surjective (Polynomial.aeval (R := k) b₀) := by
    intro b
    have hm := hmem_adjoin (e.symm (C b)).natDegree b le_rfl
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
    exact hm
  have hinj : Function.Injective (Polynomial.aeval (R := k) b₀) := by
    let ψ : k[X] →ₐ[k] k[X][X] :=
      (e.symm.toAlgHom.comp (Polynomial.CAlgHom (R := k) (A := B))).comp
        (Polynomial.aeval (R := k) b₀)
    have hψ : ψ = Polynomial.mapAlgHom (Algebra.ofId k k[X]) := by
      apply Polynomial.algHom_ext
      simp [ψ, hb₀]
    have hψ_inj : Function.Injective ψ := by
      rw [hψ]
      exact Polynomial.map_injective (algebraMap k k[X]) Polynomial.C_injective
    exact Function.Injective.of_comp
      (f := (e.symm.toAlgHom.comp (Polynomial.CAlgHom (R := k) (A := B)))) hψ_inj
  exact ⟨AlgEquiv.ofBijective (Polynomial.aeval (R := k) b₀) ⟨hinj, hsurj⟩⟩

private noncomputable def swapPoly (k : Type u) [CommRing k] : k[X][X] ≃ₐ[k] k[X][X] := by
  let innerToOuter : k[X] →ₐ[k] k[X][X] := Polynomial.mapAlgHom (Algebra.ofId k k[X])
  let toFun : k[X][X] →ₐ[k] k[X][X] :=
    Polynomial.eval₂AlgHom innerToOuter (C (X : k[X])) (fun _ => Commute.all _ _)
  have hto_C : ∀ p : k[X], toFun (C p) = p.map C := fun p => by
    simp [toFun, innerToOuter]
  have hto_X : toFun X = C X := by
    simp [toFun]
  have hinv : toFun.comp toFun = AlgHom.id k k[X][X] := by
    apply Polynomial.algHom_ext'
    · apply Polynomial.algHom_ext
      simp [hto_C, hto_X]
    · simp [hto_X, hto_C]
  exact AlgEquiv.ofAlgHom toFun toFun hinv hinv

private lemma swapPoly_C {k : Type u} [CommRing k] (p : k[X]) :
    swapPoly k (C p) = p.map C := by
  simp [swapPoly]

private lemma swapPoly_X {k : Type u} [CommRing k] :
    swapPoly k (X : k[X][X]) = C X := by
  simp [swapPoly]

private lemma swapPoly_map_C {k : Type u} [CommRing k] (p : k[X]) :
    swapPoly k (p.map C) = C p := by
  rw [← swapPoly_C p]
  exact (swapPoly k).symm_apply_apply (C p)

private lemma swapPoly_coeff_coeff {k : Type u} [CommRing k] (F : k[X][X]) (i j : ℕ) :
    ((swapPoly k F).coeff j).coeff i = (F.coeff i).coeff j := by
  induction F using Polynomial.induction_on' with
  | add F₁ F₂ h₁ h₂ =>
    simp [map_add, h₁, h₂]
  | monomial n p =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, swapPoly_C, map_pow, swapPoly_X,
      ← map_pow, Polynomial.coeff_mul_C, Polynomial.coeff_map, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X_pow]
    split_ifs <;> simp

private lemma natDegree_coeff_le_natDegree_swapPoly {k : Type u} [CommRing k]
    (F : k[X][X]) (i : ℕ) :
    (F.coeff i).natDegree ≤ (swapPoly k F).natDegree := by
  rcases eq_or_ne (F.coeff i) 0 with h0 | hne
  · simp [h0]
  · refine Polynomial.le_natDegree_of_ne_zero ?_
    intro hzero
    have hc := congrArg (fun p : k[X] => p.coeff i) hzero
    rw [swapPoly_coeff_coeff, Polynomial.coeff_zero] at hc
    exact (Polynomial.leadingCoeff_ne_zero.mpr hne) hc

private lemma subalgebra_eq_poly_of_integrally_closed {k : Type u} [Field k]
    (S : Subalgebra k k[X]) [IsIntegrallyClosed S]
    (hnonconst : ∃ u : S, 0 < u.1.natDegree) : Nonempty (k[X] ≃ₐ[k] S) := by
  classical
  have hex_deg : ∃ d : ℕ, 0 < d ∧ ∃ u : S, u.1.natDegree = d := by
    obtain ⟨u, hu⟩ := hnonconst
    exact ⟨u.1.natDegree, hu, u, rfl⟩
  let d : ℕ := Nat.find hex_deg
  have hd_spec : 0 < d ∧ ∃ u : S, u.1.natDegree = d := Nat.find_spec hex_deg
  have hd_pos : 0 < d := hd_spec.1
  obtain ⟨u, hu_deg⟩ := hd_spec.2
  have hmin : ∀ s : S, 0 < s.1.natDegree → d ≤ s.1.natDegree := by
    intro s hs
    exact Nat.find_min' hex_deg ⟨hs, s, rfl⟩
  let diffPoly : S → S[X] := fun s => s.1.map (algebraMap k S) - C s
  have hdiff_aeval : ∀ s : S, Polynomial.aeval (R := S) (X : k[X]) (diffPoly s) = 0 := by
    intro s
    dsimp [diffPoly]
    rw [map_sub (Polynomial.aeval (R := S) (X : k[X])), Polynomial.aeval_C,
      Polynomial.aeval_map_algebraMap]
    change Polynomial.aeval (X : k[X]) s.1 - s.1 = 0
    simp
  have hu_ne : u.1 ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hu_deg
    omega
  have hu_lc_ne : u.1.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hu_ne
  have hdiff_u_deg : (diffPoly u).natDegree = d := by
    dsimp [diffPoly]
    have hmap_deg : (u.1.map (algebraMap k S)).natDegree = d := by
      rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective (algebraMap k S)), hu_deg]
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · exact hmap_deg
    · simp [hmap_deg, hd_pos]
  have hdiff_u_lc : (diffPoly u).leadingCoeff = algebraMap k S u.1.leadingCoeff := by
    dsimp [diffPoly]
    have hmap_deg : (u.1.map (algebraMap k S)).natDegree = d := by
      rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective (algebraMap k S)), hu_deg]
    have hmap_ne : u.1.map (algebraMap k S) ≠ 0 := by
      intro h0
      rw [h0, Polynomial.natDegree_zero] at hmap_deg
      omega
    have hdeg_lt : (C u).degree < (u.1.map (algebraMap k S)).degree := by
      refine lt_of_le_of_lt Polynomial.degree_C_le ?_
      rw [Polynomial.degree_eq_natDegree hmap_ne, hmap_deg]
      exact_mod_cast hd_pos
    rw [Polynomial.leadingCoeff_sub_of_degree_lt hdeg_lt,
      Polynomial.leadingCoeff_map_of_injective (RingHom.injective (algebraMap k S))]
  have hX_int : IsIntegral S (X : k[X]) := by
    refine ⟨C (algebraMap k S u.1.leadingCoeff⁻¹) * diffPoly u, ?_, ?_⟩
    · rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hdiff_u_lc,
        ← map_mul, inv_mul_cancel₀ hu_lc_ne, map_one]
    · rw [← Polynomial.aeval_def, map_mul, hdiff_aeval u, mul_zero]
  let m : S[X] := minpoly S (X : k[X])
  have hm_monic : m.Monic := minpoly.monic hX_int
  have hm_dvd_u : m ∣ diffPoly u := minpoly.isIntegrallyClosed_dvd hX_int (hdiff_aeval u)
  obtain ⟨q, hq⟩ := hm_dvd_u
  have hmap_diff : (diffPoly u).map S.val.toRingHom = u.1.map C - C u.1 := by
    dsimp [diffPoly]
    rw [Polynomial.map_sub, Polynomial.map_map, Polynomial.map_C]
    rfl
  let M : k[X][X] := swapPoly k (m.map S.val.toRingHom)
  let Q : k[X][X] := swapPoly k (q.map S.val.toRingHom)
  have hMQ : C u.1 - u.1.map C = M * Q := by
    have h1 := congrArg (fun p : S[X] => swapPoly k (p.map S.val.toRingHom)) hq
    rw [hmap_diff, map_sub, swapPoly_map_C, swapPoly_C, Polynomial.map_mul, map_mul] at h1
    exact h1
  have hLHS_deg : (C u.1 - u.1.map C).natDegree = d := by
    have hmap_deg : (u.1.map C).natDegree = d := by
      rw [Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective, hu_deg]
    rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt]
    · exact hmap_deg
    · simp [hmap_deg, hd_pos]
  have hLHS_lc : (C u.1 - u.1.map C).leadingCoeff = C (-u.1.leadingCoeff) := by
    have hmap_deg : (u.1.map C).natDegree = d := by
      rw [Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective, hu_deg]
    have hmap_ne : (u.1.map C : k[X][X]) ≠ 0 := by
      intro h0
      rw [h0, Polynomial.natDegree_zero] at hmap_deg
      omega
    have hlt : (C u.1 : k[X][X]).degree < (u.1.map C).degree := by
      refine lt_of_le_of_lt Polynomial.degree_C_le ?_
      rw [Polynomial.degree_eq_natDegree hmap_ne, hmap_deg]
      exact_mod_cast hd_pos
    rw [sub_eq_add_neg, Polynomial.leadingCoeff_add_of_degree_lt (by simpa using hlt),
      Polynomial.leadingCoeff_neg, Polynomial.leadingCoeff_map_of_injective Polynomial.C_injective,
      ← map_neg]
  have hLHS_ne : (C u.1 - u.1.map C : k[X][X]) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hLHS_deg
    omega
  have hM_ne : M ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hMQ
    exact hLHS_ne hMQ
  have hQ_ne : Q ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hMQ
    exact hLHS_ne hMQ
  have hM_ge_d : d ≤ M.natDegree := by
    have hex_nonconst : ∃ i : ℕ, 0 < (m.coeff i).1.natDegree := by
      by_contra hall
      push Not at hall
      have hcoeff_C : ∀ i : ℕ, (m.coeff i).1 = C ((m.coeff i).1.coeff 0) :=
        fun i => Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp (hall i))
      let m₀ : k[X] := ∑ i ∈ m.support, C ((m.coeff i).1.coeff 0) * X ^ i
      have hm_eq : m.map S.val.toRingHom = m₀.map C := by
        apply Polynomial.ext
        intro i
        rw [Polynomial.coeff_map, Polynomial.coeff_map]
        dsimp [m₀]
        rw [Polynomial.finsetSum_coeff]
        by_cases hi : i ∈ m.support
        · rw [Finset.sum_eq_single i]
          · simp only [Polynomial.coeff_C_mul_X_pow, ↓reduceIte]
            exact hcoeff_C i
          · intro j _ hne
            simp [hne.symm]
          · intro hmem
            exact absurd hi hmem
        · rw [Finset.sum_eq_zero]
          · have hm0 : m.coeff i = 0 := Polynomial.notMem_support_iff.mp hi
            simp [hm0]
          · intro j hj
            have hne : i ≠ j := fun h => hi (h ▸ hj)
            simp [hne]
      have hm₀_zero : m₀ = 0 := by
        have haeval : Polynomial.aeval (X : k[X]) m = 0 := minpoly.aeval S (X : k[X])
        have h1 : (m.map S.val.toRingHom).eval (X : k[X]) = 0 := by
          rw [Polynomial.eval_map]
          exact haeval
        rw [hm_eq, Polynomial.eval_map] at h1
        have h2 : Polynomial.eval₂ C (X : k[X]) m₀ = m₀ := Polynomial.eval₂_C_X
        exact h2.symm.trans h1
      have hm_zero : m = 0 := by
        apply Polynomial.ext
        intro i
        apply Subtype.ext
        rw [Polynomial.coeff_zero, ZeroMemClass.coe_zero, hcoeff_C i]
        have hi0 : m₀.coeff i = 0 := by rw [hm₀_zero, Polynomial.coeff_zero]
        dsimp [m₀] at hi0
        rw [Polynomial.finsetSum_coeff] at hi0
        by_cases hi : i ∈ m.support
        · rw [Finset.sum_eq_single i] at hi0
          · simp only [Polynomial.coeff_C_mul_X_pow, ↓reduceIte] at hi0
            simp [hi0]
          · intro j _ hne
            simp [hne.symm]
          · intro hmem
            exact absurd hi hmem
        · have : m.coeff i = 0 := Polynomial.notMem_support_iff.mp hi
          simp [this]
      exact hm_monic.ne_zero hm_zero
    obtain ⟨i, hi⟩ := hex_nonconst
    calc d ≤ (m.coeff i).1.natDegree := hmin (m.coeff i) hi
      _ = ((m.map S.val.toRingHom).coeff i).natDegree := by simp
      _ ≤ M.natDegree := natDegree_coeff_le_natDegree_swapPoly _ i
  have hQ_deg0 : Q.natDegree = 0 := by
    have hmul : (M * Q).natDegree = M.natDegree + Q.natDegree :=
      Polynomial.natDegree_mul hM_ne hQ_ne
    rw [← hMQ, hLHS_deg] at hmul
    omega
  have hQ_C : Q = C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hQ_deg0
  have hQ0_ne : Q.coeff 0 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hQ_C
    exact hQ_ne hQ_C
  have hQ0_deg0 : (Q.coeff 0).natDegree = 0 := by
    have hlc := congrArg Polynomial.leadingCoeff hMQ
    rw [hLHS_lc, Polynomial.leadingCoeff_mul, hQ_C, Polynomial.leadingCoeff_C] at hlc
    have hMlc_ne : M.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hM_ne
    have hdeg := congrArg Polynomial.natDegree hlc
    rw [Polynomial.natDegree_C, Polynomial.natDegree_mul hMlc_ne hQ0_ne] at hdeg
    omega
  let c : k := (Q.coeff 0).coeff 0
  have hQ0_eq_Cc : Q.coeff 0 = C c := Polynomial.eq_C_of_natDegree_eq_zero hQ0_deg0
  have hc_ne : c ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hQ0_eq_Cc
    exact hQ0_ne hQ0_eq_Cc
  have hQ_CC : Q = C (C c) := by
    rw [hQ_C, hQ0_eq_Cc]
  have hq_C : q = C (algebraMap k S c) := by
    have h1 : q.map S.val.toRingHom = C (C c) := by
      have h2 := congrArg (swapPoly k).symm hQ_CC
      have h3 : (swapPoly k).symm (C (C c)) = C (C c) := by
        apply (swapPoly k).injective
        simp [swapPoly_C]
      simpa [Q, h3] using h2
    apply Polynomial.map_injective S.val.toRingHom Subtype.val_injective
    rw [h1, Polynomial.map_C]
    rfl
  have hu_dvd_m : diffPoly u ∣ m := by
    refine ⟨C (algebraMap k S c⁻¹), ?_⟩
    rw [hq, hq_C, mul_assoc, ← map_mul, ← map_mul, mul_inv_cancel₀ hc_ne, map_one, map_one,
      mul_one]
  have hmem_adjoin : ∀ n : ℕ, ∀ s : S, s.1.natDegree ≤ n →
      s.1 ∈ Algebra.adjoin k ({u.1} : Set k[X]) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs_deg
      have hdiv_s : diffPoly u ∣ diffPoly s :=
        dvd_trans hu_dvd_m (minpoly.isIntegrallyClosed_dvd hX_int (hdiff_aeval s))
      obtain ⟨g, hg⟩ := hdiv_s
      have hg0 := congrArg (fun p : S[X] => p.coeff 0) hg
      simp only [diffPoly, Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_C_zero,
        Polynomial.mul_coeff_zero] at hg0
      have hg0_val := congrArg Subtype.val hg0
      simp only [Subalgebra.coe_sub, Subalgebra.coe_mul] at hg0_val
      have hs_eq : s.1 = C (s.1.coeff 0) + (u.1 - C (u.1.coeff 0)) * (g.coeff 0).1 := by
        change C (s.1.coeff 0) - s.1 = (C (u.1.coeff 0) - u.1) * (g.coeff 0).1 at hg0_val
        linear_combination -hg0_val
      rcases eq_or_ne (g.coeff 0).1 0 with h0 | hne
      · rw [h0, mul_zero, add_zero] at hs_eq
        rw [hs_eq]
        exact Subalgebra.algebraMap_mem _ (s.1.coeff 0)
      · have hu_sub_deg : (u.1 - C (u.1.coeff 0)).natDegree = d := by
          rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
          · exact hu_deg
          · simp [hu_deg, hd_pos]
        have hu_sub_ne : u.1 - C (u.1.coeff 0) ≠ 0 := by
          intro h0
          rw [h0, Polynomial.natDegree_zero] at hu_sub_deg
          omega
        have hprod_deg : ((u.1 - C (u.1.coeff 0)) * (g.coeff 0).1).natDegree =
            d + (g.coeff 0).1.natDegree := by
          rw [Polynomial.natDegree_mul hu_sub_ne hne, hu_sub_deg]
        have hs_deg_eq : s.1.natDegree = d + (g.coeff 0).1.natDegree := by
          rw [hs_eq, Polynomial.natDegree_add_eq_right_of_natDegree_lt]
          · exact hprod_deg
          · rw [hprod_deg]
            have : (C (s.1.coeff 0) : k[X]).natDegree = 0 := Polynomial.natDegree_C _
            omega
        have hg0_lt : (g.coeff 0).1.natDegree < n := by omega
        have hg0_mem : (g.coeff 0).1 ∈ Algebra.adjoin k ({u.1} : Set k[X]) :=
          ih (g.coeff 0).1.natDegree hg0_lt (g.coeff 0) le_rfl
        rw [hs_eq]
        refine Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _)
          (Subalgebra.mul_mem _ (Subalgebra.sub_mem _ (Algebra.subset_adjoin rfl)
            (Subalgebra.algebraMap_mem _ _)) hg0_mem)
  have hsurj : Function.Surjective (Polynomial.aeval (R := k) u) := by
    intro s
    have hmem := hmem_adjoin s.1.natDegree s le_rfl
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
    obtain ⟨p, hp⟩ := hmem
    refine ⟨p, Subtype.ext ?_⟩
    have hval : (Polynomial.aeval (R := k) u p).1 = Polynomial.aeval (R := k) u.1 p := by
      have := Polynomial.aeval_algHom_apply S.val u p
      exact this.symm
    exact hval.trans hp
  have hinj : Function.Injective (Polynomial.aeval (R := k) u) := by
    intro p₁ p₂ h
    have hval : Polynomial.aeval (R := k) u.1 p₁ = Polynomial.aeval (R := k) u.1 p₂ := by
      have h1 : Polynomial.aeval (R := k) u.1 p₁ = S.val (Polynomial.aeval (R := k) u p₁) :=
        Polynomial.aeval_algHom_apply S.val u p₁
      have h2 : Polynomial.aeval (R := k) u.1 p₂ = S.val (Polynomial.aeval (R := k) u p₂) :=
        Polynomial.aeval_algHom_apply S.val u p₂
      rw [h1, h2, h]
    have hsub : (p₁ - p₂).comp u.1 = 0 := by
      have hcomp : (p₁ - p₂).comp u.1 = Polynomial.aeval (R := k) u.1 (p₁ - p₂) := rfl
      rw [hcomp, map_sub, hval, sub_self]
    by_contra hne
    have hsub_ne : p₁ - p₂ ≠ 0 := sub_ne_zero.mpr hne
    have hdeg := Polynomial.natDegree_comp (p := p₁ - p₂) (q := u.1)
    rw [hsub, Polynomial.natDegree_zero, hu_deg] at hdeg
    have hdeg0 : (p₁ - p₂).natDegree = 0 :=
      (mul_eq_zero.mp hdeg.symm).resolve_right hd_pos.ne'
    have hC := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
    rw [hC, Polynomial.C_comp] at hsub
    exact hsub_ne (hC.trans hsub)
  exact ⟨AlgEquiv.ofBijective (Polynomial.aeval (R := k) u) ⟨hinj, hsurj⟩⟩

end OMA.ZariskiDimOne

theorem OMA.solution :
    type_of% @Arxiv.«2208.14736».zariski_cancellation_problem.variants.dim_one := by
  intro k _ B _ _ _ ⟨e⟩
  have : IsDomain B := OMA.ZariskiDimOne.isDomain_of_poly_equiv e
  have : IsIntegrallyClosed B := OMA.ZariskiDimOne.isIntegrallyClosed_of_poly_equiv e
  by_cases hX : ∃ b₀ : B, e.symm (C b₀) = X
  · obtain ⟨b₀, hb₀⟩ := hX
    exact OMA.ZariskiDimOne.case_X_in_range e b₀ hb₀
  · let ev0 : k[X][X] →ₐ[k] k[X] := (Polynomial.aeval (R := k[X]) (0 : k[X])).restrictScalars k
    let f₀ : B →ₐ[k] k[X] :=
      ev0.comp (e.symm.toAlgHom.comp (Polynomial.CAlgHom (R := k) (A := B)))
    have hf₀_inj : Function.Injective f₀ := by
      rw [injective_iff_map_eq_zero]
      intro b hb
      by_contra hb0
      have he_ne : e.symm (C b) ≠ 0 := fun h0 =>
        hb0 (Polynomial.C_injective (e.symm.injective (by simpa using h0)))
      have hXdvd : X ∣ e.symm (C b) := by
        rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
        exact hb
      obtain ⟨g, hg⟩ := hXdvd
      have hg_ne : g ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hg
        exact he_ne hg
      have heq : C b = e X * e g := by
        have := congrArg e hg
        simpa [map_mul] using this
      have heX_ne : e X ≠ 0 := fun h0 => by simp at h0
      have heg_ne : e g ≠ 0 := fun h0 =>
        hg_ne (e.injective (by simpa using h0))
      have hdeg := congrArg Polynomial.natDegree heq
      rw [Polynomial.natDegree_C, Polynomial.natDegree_mul heX_ne heg_ne] at hdeg
      have heX_deg0 : (e X).natDegree = 0 := by omega
      have heX_C : e X = C ((e X).coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero heX_deg0
      exact hX ⟨(e X).coeff 0, by rw [← heX_C, e.symm_apply_apply]⟩
    let S : Subalgebra k k[X] := f₀.range
    let eBS : B ≃ₐ[k] S := AlgEquiv.ofInjective f₀ hf₀_inj
    have hIC_S : IsIntegrallyClosed S := by
      rw [isIntegrallyClosed_iff (FractionRing S)]
      intro x hx
      have hj_inj : Function.Injective
          ((algebraMap B (FractionRing B)).comp eBS.symm.toRingHom) :=
        (IsFractionRing.injective B (FractionRing B)).comp eBS.symm.injective
      let j : FractionRing S →+* FractionRing B := IsFractionRing.lift hj_inj
      have hj_alg : ∀ s : S, j (algebraMap S (FractionRing S) s) =
          algebraMap B (FractionRing B) (eBS.symm s) :=
        fun s => IsFractionRing.lift_algebraMap hj_inj s
      obtain ⟨P, hP_monic, hPx⟩ := hx
      have hP'_monic : (P.map eBS.symm.toRingHom).Monic := hP_monic.map _
      have hP'_eval : Polynomial.aeval (j x) (P.map eBS.symm.toRingHom) = 0 := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_map]
        have hcomp : (algebraMap B (FractionRing B)).comp eBS.symm.toRingHom =
            j.comp (algebraMap S (FractionRing S)) := by
          ext s
          exact (hj_alg s).symm
        rw [hcomp, ← Polynomial.hom_eval₂]
        simpa [Polynomial.aeval_def] using congrArg j hPx
      obtain ⟨b, hb⟩ := (isIntegrallyClosed_iff (FractionRing B)).mp inferInstance
        ⟨P.map eBS.symm.toRingHom, hP'_monic, hP'_eval⟩
      refine ⟨eBS b, (RingHom.injective j) ?_⟩
      rw [hj_alg, eBS.symm_apply_apply, hb]
    have hnonconst : ∃ u : S, 0 < u.1.natDegree := by
      obtain ⟨b, hb⟩ := OMA.ZariskiDimOne.not_surjective_algebraMap_of_poly_equiv e
      refine ⟨eBS b, ?_⟩
      rcases Nat.eq_zero_or_pos (eBS b).1.natDegree with h0 | hpos
      · exfalso
        have hC := Polynomial.eq_C_of_natDegree_eq_zero h0
        have hf : f₀ b = f₀ (algebraMap k B ((eBS b).1.coeff 0)) := by
          rw [AlgHom.commutes]
          exact hC
        exact hb ⟨(eBS b).1.coeff 0, (hf₀_inj hf).symm⟩
      · exact hpos
    have : IsIntegrallyClosed S := hIC_S
    obtain ⟨eS⟩ := OMA.ZariskiDimOne.subalgebra_eq_poly_of_integrally_closed S hnonconst
    exact ⟨eS.trans eBS.symm⟩
