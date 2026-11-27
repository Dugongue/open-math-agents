import FormalConjectures.Paper.KaplanskyUInvariant

/-!
# Proof that the u-invariant of a field is never 7

We prove `¬ KaplanskyUInvariant.IsUInvariant 7` (Elman–Lam 1973; Lam 2005, Prop. XI.6.8)
by an elementary algebraic argument over any field `F` of characteristic not `2`:

1. Assume `u(F) = 7`, so there is an anisotropic 7-dimensional diagonal form `w` and every
   8-dimensional diagonal form is isotropic.
2. Since `w ⊥ ⟨det w⟩` has dimension 8, it is isotropic, so `w` represents `-det w`.
   Splitting off its orthogonal complement and rescaling yields an anisotropic 7-dimensional
   form `⟨1, b₀, b₁, b₂, b₃, b₄, b₅⟩` with `b₀ b₁ b₂ b₃ b₄ b₅ = -t²` (`t ≠ 0`).
3. Using Euler's four-square identity and the isotropy of 8-dimensional 3-fold Pfister forms,
   every 2-fold Pfister form `pf4 u v = ⟨1, u, v, u v⟩` (with `u, v ≠ 0`) is universal, and
   hence invariant under nonzero scaling (`s • pf4 u v ≅ pf4 u v`).
4. Setting `s = b₀ b₁ b₂`, the 8-dimensional sum `⟨s, -s⟩ ⊥ γ` (where `γ = ⟨b₀, ..., b₅⟩`)
   decomposes into two scaled 2-fold Pfister forms, hence is isometric to
   `⟨1, -1⟩ ⊥ ⟨u₁, v₁, u₁ v₁, -u₂, -v₂, -u₂ v₂⟩`.
5. Applying 1-dimensional Witt cancellation (via a Householder reflection) twice cancels
   `⟨1, -1⟩ ≅ ⟨s, -s⟩`, giving `γ ≅ ⟨u₁, v₁, u₁ v₁, -u₂, -v₂, -u₂ v₂⟩`.
6. Finally, universality of `pf4 u₁ v₁` yields a representation of `u₂`, producing a nonzero
   isotropic vector of `⟨1⟩ ⊥ γ`, contradicting anisotropy.
-/

namespace OMA_KaplanskyNotSeven

open QuadraticMap QuadraticForm

section Pfister

variable {F : Type} [Field F]

/-- The 2-fold Pfister form `⟨1, u, v, u * v⟩` on `Fin 4 → F`. -/
private def pf4 (u v : F) (x : Fin 4 → F) : F :=
  x 0 ^ 2 + u * x 1 ^ 2 + v * x 2 ^ 2 + u * v * x 3 ^ 2

/-- Multiplication in the quaternion algebra `(-u, -v / F)`. -/
private def qmul (u v : F) (a b : Fin 4 → F) : Fin 4 → F :=
  ![a 0 * b 0 - u * a 1 * b 1 - v * a 2 * b 2 - u * v * a 3 * b 3,
    a 0 * b 1 + a 1 * b 0 + v * a 2 * b 3 - v * a 3 * b 2,
    a 0 * b 2 - u * a 1 * b 3 + a 2 * b 0 + u * a 3 * b 1,
    a 0 * b 3 + a 1 * b 2 - a 2 * b 1 + a 3 * b 0]

/-- Conjugation in the quaternion algebra `(-u, -v / F)`. -/
private def qconj (a : Fin 4 → F) : Fin 4 → F :=
  ![a 0, -a 1, -a 2, -a 3]

private lemma pf4_qconj (u v : F) (a : Fin 4 → F) : pf4 u v (qconj a) = pf4 u v a := by
  simp only [pf4, qconj, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

private lemma pf4_qmul (u v : F) (a b : Fin 4 → F) :
    pf4 u v (qmul u v a b) = pf4 u v a * pf4 u v b := by
  simp only [pf4, qmul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

private lemma pf4_smul (u v c : F) (a : Fin 4 → F) :
    pf4 u v (c • a) = c ^ 2 * pf4 u v a := by
  simp only [pf4, Pi.smul_apply, smul_eq_mul]
  ring

private lemma qmul_conj_left (u v : F) (p x : Fin 4 → F) :
    qmul u v (qconj p) (qmul u v p x) = (pf4 u v p) • x := by
  funext i
  fin_cases i <;> simp [qmul, qconj, pf4] <;> ring

private lemma qmul_conj_right (u v : F) (p x : Fin 4 → F) :
    qmul u v p (qmul u v (qconj p) x) = (pf4 u v p) • x := by
  funext i
  fin_cases i <;> simp [qmul, qconj, pf4] <;> ring

/-- Left multiplication by `p` as a linear equivalence when `pf4 u v p = s ≠ 0`. -/
private def qmulEquiv (u v s : F) (hs : s ≠ 0) (p : Fin 4 → F) (hp : pf4 u v p = s) :
    (Fin 4 → F) ≃ₗ[F] (Fin 4 → F) where
  toFun := qmul u v p
  map_add' x y := by
    funext i
    fin_cases i <;> simp [qmul] <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp [qmul] <;> ring
  invFun y := s⁻¹ • qmul u v (qconj p) y
  left_inv x := by
    dsimp only
    have h := qmul_conj_left u v p x
    rw [hp] at h
    rw [h, smul_smul, inv_mul_cancel₀ hs, one_smul]
  right_inv y := by
    dsimp only
    have hsmul : qmul u v p (s⁻¹ • qmul u v (qconj p) y) =
        s⁻¹ • qmul u v p (qmul u v (qconj p) y) := by
      funext i
      fin_cases i <;> simp [qmul] <;> ring
    rw [hsmul, qmul_conj_right, hp, smul_smul, inv_mul_cancel₀ hs, one_smul]

/-- If every 8-dimensional diagonal form over `F` is isotropic, then every 2-fold Pfister form
`pf4 u v` with `u, v ≠ 0` is universal. -/
private lemma pf4_universal [NeZero (2 : F)]
    (h8 : ∀ w : Fin 8 → F, ∃ z : Fin 8 → F, z ≠ 0 ∧ weightedSumSquares F w z = 0)
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (c : F) :
    ∃ x : Fin 4 → F, pf4 u v x = c := by
  by_cases hiso : ∃ a : Fin 4 → F, a ≠ 0 ∧ pf4 u v a = 0
  · obtain ⟨a, ha_ne, ha_eq⟩ := hiso
    have hex : ∃ k : Fin 4, a k ≠ 0 := by
      by_contra h
      push Not at h
      exact ha_ne (funext h)
    obtain ⟨k, hk⟩ := hex
    let w4 : Fin 4 → F := ![1, u, v, u * v]
    have hw4 : w4 k ≠ 0 := by
      fin_cases k
      · exact one_ne_zero
      · exact hu
      · exact hv
      · exact mul_ne_zero hu hv
    have hpf4_eq : ∀ x : Fin 4 → F, pf4 u v x = ∑ i : Fin 4, w4 i * x i ^ 2 := by
      intro x
      simp only [pf4, w4, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      ring
    let e : Fin 4 → F := Pi.single k (1 : F)
    let t : F := (c - pf4 u v e) / (2 * w4 k * a k)
    refine ⟨t • a + e, ?_⟩
    have hden : 2 * w4 k * a k ≠ 0 :=
      mul_ne_zero (mul_ne_zero (NeZero.ne (2 : F)) hw4) hk
    have hexp : pf4 u v (t • a + e) =
        t ^ 2 * pf4 u v a + 2 * t * (∑ i : Fin 4, w4 i * a i * e i) + pf4 u v e := by
      simp only [hpf4_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    have hcross : ∑ i : Fin 4, w4 i * a i * e i = w4 k * a k := by
      rw [Finset.sum_eq_single k]
      · simp [e]
      · intro i _ hi; simp [e, hi]
      · intro hk'; exact absurd (Finset.mem_univ k) hk'
    rw [hexp, ha_eq, mul_zero, zero_add, hcross]
    simp only [t]
    field_simp [hden]
    ring
  · push Not at hiso
    let w8 : Fin 8 → F := ![1, u, v, u * v, -c, -c * u, -c * v, -c * u * v]
    obtain ⟨z, hz_ne, hz_eq⟩ := h8 w8
    let a : Fin 4 → F := ![z 0, z 1, z 2, z 3]
    let b : Fin 4 → F := ![z 4, z 5, z 6, z 7]
    have hrel : pf4 u v a - c * pf4 u v b = 0 := by
      have hw8_5 : w8 5 = -c * u := rfl
      have hw8_6 : w8 6 = -c * v := rfl
      have hw8_7 : w8 7 = -c * u * v := rfl
      rw [weightedSumSquares_apply, Fin.sum_univ_eight] at hz_eq
      simp only [smul_eq_mul] at hz_eq
      rw [hw8_5, hw8_6, hw8_7] at hz_eq
      simp only [w8, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] at hz_eq
      simp only [pf4, a, b, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      linear_combination hz_eq
    have hb_ne : b ≠ 0 := by
      intro hb0
      have hpb0 : pf4 u v b = 0 := by simp [pf4, hb0]
      have hpa0 : pf4 u v a = 0 := by rw [hpb0, mul_zero, sub_zero] at hrel; exact hrel
      have ha0 : a = 0 := by_contra fun ha_ne => hiso a ha_ne hpa0
      apply hz_ne
      funext i
      fin_cases i
      · exact congr_fun ha0 0
      · exact congr_fun ha0 1
      · exact congr_fun ha0 2
      · exact congr_fun ha0 3
      · exact congr_fun hb0 0
      · exact congr_fun hb0 1
      · exact congr_fun hb0 2
      · exact congr_fun hb0 3
    have hpb_ne : pf4 u v b ≠ 0 := hiso b hb_ne
    refine ⟨(pf4 u v b)⁻¹ • qmul u v a (qconj b), ?_⟩
    rw [pf4_smul, pf4_qmul, pf4_qconj]
    have hpa : pf4 u v a = c * pf4 u v b := sub_eq_zero.mp hrel
    rw [hpa]
    field_simp [hpb_ne]

end Pfister

section WittCancel

variable {F : Type} [Field F] [NeZero (2 : F)]

/-- 1-dimensional Witt cancellation via a Householder reflection:
if `a * t² + Q₁ x ≅ a * t² + Q₂ y` with `a ≠ 0`, then `Q₁ ≅ Q₂`. -/
private lemma witt_cancel_one {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁]
    [AddCommGroup V₂] [Module F V₂]
    (Q₁ : QuadraticForm F V₁) (Q₂ : QuadraticForm F V₂)
    (a : F) (ha : a ≠ 0)
    (E : (F × V₁) ≃ₗ[F] (F × V₂))
    (hE : ∀ p : F × V₁, a * (E p).1 ^ 2 + Q₂ (E p).2 = a * p.1 ^ 2 + Q₁ p.2) :
    ∃ E' : V₁ ≃ₗ[F] V₂, ∀ x : V₁, Q₂ (E' x) = Q₁ x := by
  let Q1t : QuadraticForm F (F × V₁) :=
    (a • (QuadraticMap.sq (R := F))).prod Q₁
  let Q2t : QuadraticForm F (F × V₂) :=
    (a • (QuadraticMap.sq (R := F))).prod Q₂
  have hQ1t : ∀ p : F × V₁, Q1t p = a * p.1 ^ 2 + Q₁ p.2 := by
    intro p; simp [Q1t, _root_.sq]
  have hQ2t : ∀ q : F × V₂, Q2t q = a * q.1 ^ 2 + Q₂ q.2 := by
    intro q; simp [Q2t, _root_.sq]
  have hEt : ∀ p : F × V₁, Q2t (E p) = Q1t p := fun p => by rw [hQ2t, hQ1t, hE]
  let B2 := QuadraticMap.polarBilin Q2t
  have hB2_add : ∀ x y : F × V₂, Q2t (x + y) = Q2t x + Q2t y + B2 x y := fun x y => by
    simp only [B2, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
    ring
  have hB2_diag : ∀ z : F × V₂, B2 z z = 2 * Q2t z := fun z => by
    simp only [B2, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
    have h2z : z + z = (2 : F) • z := by rw [two_smul]
    rw [h2z, QuadraticMap.map_smul Q2t, smul_eq_mul]
    ring
  have hB2_symm : ∀ x y : F × V₂, B2 x y = B2 y x := fun x y => by
    simp only [B2, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, add_comm]
    ring
  let e1 : F × V₁ := (1, 0)
  let e2 : F × V₂ := (1, 0)
  let w : F × V₂ := E e1
  have hQe2 : Q2t e2 = a := by simp [hQ2t, e2]
  have hQw : Q2t w = a := by rw [show w = E e1 from rfl, hEt, hQ1t]; simp [e1]
  have hpar : Q2t (e2 + w) + Q2t (e2 - w) = 4 * a := by
    have h1 := hB2_add e2 w
    have h2 := hB2_add e2 (-w)
    rw [QuadraticMap.map_neg Q2t, map_neg] at h2
    rw [sub_eq_add_neg]
    linear_combination h1 + h2 + 2 * hQe2 + 2 * hQw
  have h4a : (4 : F) * a ≠ 0 := by
    have h2 : (2 : F) ≠ 0 := NeZero.ne (2 : F)
    have h4 : (4 : F) = 2 * 2 := by ring
    rw [h4]
    exact mul_ne_zero (mul_ne_zero h2 h2) ha
  have hsign : ∃ ε : F, ε ^ 2 = 1 ∧ Q2t (e2 - ε • w) ≠ 0 := by
    by_cases hp : Q2t (e2 + w) ≠ 0
    · refine ⟨-1, by ring, ?_⟩
      simpa [sub_eq_add_neg] using hp
    · push Not at hp
      refine ⟨1, by ring, ?_⟩
      rw [one_smul]
      intro hm
      rw [hp, hm, add_zero] at hpar
      exact h4a hpar.symm
  obtain ⟨ε, hε2, hu_ne⟩ := hsign
  have hε_mul : ε * ε = 1 := by simpa [_root_.sq] using hε2
  let u : F × V₂ := e2 - ε • w
  have hu_ne' : Q2t u ≠ 0 := hu_ne
  let R : (F × V₂) →ₗ[F] (F × V₂) :=
    LinearMap.id - ((Q2t u)⁻¹ • (B2 u)).smulRight u
  have hR_apply : ∀ z : F × V₂, R z = z - (B2 u z / Q2t u) • u := by
    intro z
    simp only [R, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      LinearMap.smul_apply, smul_eq_mul, div_eq_inv_mul]
  have hR_inv : ∀ z : F × V₂, R (R z) = z := by
    intro z
    rw [hR_apply, hR_apply, map_sub (B2 u), map_smul (B2 u), smul_eq_mul, hB2_diag]
    have hcoeff : (B2 u z - B2 u z / Q2t u * (2 * Q2t u)) / Q2t u = -(B2 u z / Q2t u) := by
      field_simp [hu_ne']; ring
    rw [hcoeff, neg_smul, sub_neg_eq_add, sub_add_cancel]
  have hR_iso : ∀ z : F × V₂, Q2t (R z) = Q2t z := by
    intro z
    rw [hR_apply, sub_eq_add_neg, hB2_add, QuadraticMap.map_neg Q2t, QuadraticMap.map_smul Q2t,
      smul_eq_mul, map_neg (B2 z), map_smul (B2 z), smul_eq_mul, hB2_symm z u]
    field_simp [hu_ne']
    ring
  have hRw : R w = ε • e2 := by
    have hQu : Q2t u = 2 * a - ε * B2 e2 w := by
      have : u = e2 + (-(ε • w)) := by simp [u, sub_eq_add_neg]
      rw [this, hB2_add, QuadraticMap.map_neg Q2t, QuadraticMap.map_smul Q2t, smul_eq_mul,
        hε_mul, one_mul, hQe2, hQw, map_neg (B2 e2), map_smul (B2 e2), smul_eq_mul]
      ring
    have hBuw : B2 u w = B2 e2 w - 2 * ε * a := by
      have h1 : B2 (e2 - ε • w) w = B2 e2 w - ε * B2 w w := by
        simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [show u = e2 - ε • w from rfl, h1, hB2_diag, hQw]
      ring
    have hratio : B2 u w / Q2t u = -ε := by
      rw [div_eq_iff hu_ne', hQu, hBuw]
      linear_combination (-B2 e2 w) * hε2
    rw [hR_apply, hratio, neg_smul, sub_neg_eq_add]
    simp only [u, smul_sub, smul_smul, hε_mul, one_smul]
    abel
  let R_equiv : (F × V₂) ≃ₗ[F] (F × V₂) :=
    LinearEquiv.ofLinearMap R R (LinearMap.ext hR_inv) (LinearMap.ext hR_inv)
  let S_equiv : (F × V₂) ≃ₗ[F] (F × V₂) :=
    { toFun := fun z => ε • R_equiv z
      map_add' := fun x y => by rw [map_add, smul_add]
      map_smul' := fun c x => by rw [map_smul, smul_comm]; rfl
      invFun := fun z => ε • R_equiv.symm z
      left_inv := fun z => by
        change ε • R (ε • R z) = z
        rw [map_smul, smul_smul, hε_mul, one_smul, hR_inv]
      right_inv := fun z => by
        change ε • R (ε • R z) = z
        rw [map_smul, smul_smul, hε_mul, one_smul, hR_inv] }
  let E1 : (F × V₁) ≃ₗ[F] (F × V₂) := E.trans S_equiv
  have hE1_iso : ∀ p : F × V₁, Q2t (E1 p) = Q1t p := by
    intro p
    show Q2t (ε • R (E p)) = Q1t p
    rw [QuadraticMap.map_smul Q2t, smul_eq_mul, hε_mul, one_mul, hR_iso, hEt]
  have hE1_e1 : E1 e1 = e2 := by
    show ε • R w = e2
    rw [hRw, smul_smul, hε_mul, one_smul]
  have hE1_fst : ∀ x : V₁, (E1 (0, x)).1 = 0 := by
    intro x
    have h1 := hE1_iso (e1 + (0, x))
    rw [map_add, hE1_e1] at h1
    have hL : Q2t (e2 + E1 (0, x)) = a * (1 + (E1 (0, x)).1) ^ 2 + Q₂ (E1 (0, x)).2 := by
      rw [hQ2t]; simp [e2]
    have hR : Q1t (e1 + (0, x)) = a + Q₁ x := by
      rw [hQ1t]; simp [e1]
    have h0 := hE1_iso (0, x)
    rw [hQ2t, hQ1t] at h0
    have h0' : a * (E1 (0, x)).1 ^ 2 + Q₂ (E1 (0, x)).2 = Q₁ x := by
      linear_combination h0
    rw [hL, hR] at h1
    have h2a : 2 * a * (E1 (0, x)).1 = 0 := by linear_combination h1 - h0'
    exact (mul_eq_zero.mp h2a).resolve_left (mul_ne_zero (NeZero.ne (2 : F)) ha)
  have hE1_symm_fst : ∀ y : V₂, (E1.symm (0, y)).1 = 0 := by
    intro y
    have h1 := hE1_iso (e1 + E1.symm (0, y))
    rw [map_add, hE1_e1, E1.apply_symm_apply] at h1
    have hL : Q2t (e2 + (0, y)) = a + Q₂ y := by rw [hQ2t]; simp [e2]
    have hR : Q1t (e1 + E1.symm (0, y)) =
        a * (1 + (E1.symm (0, y)).1) ^ 2 + Q₁ (E1.symm (0, y)).2 := by
      rw [hQ1t]; simp [e1]
    have h0 := hE1_iso (E1.symm (0, y))
    rw [E1.apply_symm_apply, hQ2t, hQ1t] at h0
    have h0' : Q₂ y = a * (E1.symm (0, y)).1 ^ 2 + Q₁ (E1.symm (0, y)).2 := by
      linear_combination h0
    rw [hL, hR] at h1
    have h2a : 2 * a * (E1.symm (0, y)).1 = 0 := by linear_combination h0' - h1
    exact (mul_eq_zero.mp h2a).resolve_left (mul_ne_zero (NeZero.ne (2 : F)) ha)
  refine ⟨{
    toFun := fun x => (E1 (0, x)).2
    map_add' := fun x y => by
      have : ((0 : F), x + y) = (0, x) + (0, y) := by ext <;> simp
      rw [this, map_add]; rfl
    map_smul' := fun c x => by
      have : ((0 : F), c • x) = c • (0, x) := by ext <;> simp
      rw [this, map_smul]; rfl
    invFun := fun y => (E1.symm (0, y)).2
    left_inv := fun x => by
      dsimp only
      have h : ((0 : F), (E1 (0, x)).2) = E1 (0, x) := Prod.ext (hE1_fst x).symm rfl
      rw [h, E1.symm_apply_apply]
    right_inv := fun y => by
      dsimp only
      have h : ((0 : F), (E1.symm (0, y)).2) = E1.symm (0, y) :=
        Prod.ext (hE1_symm_fst y).symm rfl
      rw [h, E1.apply_symm_apply] }, ?_⟩
  intro x
  have h := hE1_iso (0, x)
  rw [hQ2t, hQ1t, hE1_fst x] at h
  simpa using h

end WittCancel

end OMA_KaplanskyNotSeven

set_option maxHeartbeats 600000 in
open QuadraticMap QuadraticForm OMA_KaplanskyNotSeven in
theorem OMA.solution : type_of% @KaplanskyUInvariant.u_invariant_values.variants.not_seven := by
  rintro ⟨F, _, _, hmax, hub⟩
  have : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
  -- Every 8-dimensional diagonal form is isotropic
  have h8_iso : ∀ w : Fin 8 → F, ∃ z : Fin 8 → F, z ≠ 0 ∧ weightedSumSquares F w z = 0 := by
    intro w
    by_contra h
    push Not at h
    have h8_mem : 8 ∈ anisotropicDims F :=
      mem_anisotropicDims_iff.mpr ⟨weightedSumSquares F w,
        fun x hx => by_contra fun hx0 => h x hx0 hx⟩
    have := hub h8_mem
    omega
  -- Step 1: Diagonalize an anisotropic 7-dimensional quadratic form
  obtain ⟨Q, hQ⟩ := mem_anisotropicDims_iff.mp hmax
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares
  have hQ0 : (weightedSumSquares F w).Anisotropic := by
    intro v hv
    have h0 : Q (e.symm v) = 0 := by
      rw [← e.map_app (e.symm v)]
      simpa using hv
    simpa using hQ _ h0
  have hm : Module.finrank F (Fin 7 → F) = 7 := by simp
  generalize Module.finrank F (Fin 7 → F) = m at w hQ0 hm
  subst hm
  have hw : ∀ i : Fin 7, w i ≠ 0 := by
    intro i hi
    have h0 : weightedSumSquares F w (Pi.single i (1 : F)) = 0 := by
      simp [weightedSumSquares_apply, Pi.single_apply, hi]
    exact (one_ne_zero : (1 : F) ≠ 0) (by simpa using congr_fun (hQ0 _ h0) i)
  set d : F := ∏ i : Fin 7, w i
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hw i
  -- Step 2: Find v₀ with weightedSumSquares F w v₀ = -d
  let w₈ : Fin 8 → F := ![w 0, w 1, w 2, w 3, w 4, w 5, w 6, d]
  obtain ⟨z, hz_ne, hz_eq⟩ := h8_iso w₈
  have hz_sum : ∑ i : Fin 7, w i * z i.castSucc ^ 2 + d * z 7 ^ 2 = 0 := by
    have hw₈ : ∀ i : Fin 7, w₈ i.castSucc = w i := fun i => by fin_cases i <;> rfl
    have hw₈_7 : w₈ (Fin.last 7) = d := rfl
    have hlast : z (Fin.last 7) = z 7 := rfl
    rw [weightedSumSquares_apply, Fin.sum_univ_castSucc] at hz_eq
    simp only [smul_eq_mul] at hz_eq
    rw [hw₈_7, hlast] at hz_eq
    have hsum7 : ∑ i : Fin 7, w₈ i.castSucc * (z i.castSucc * z i.castSucc) =
        ∑ i : Fin 7, w i * z i.castSucc ^ 2 :=
      Finset.sum_congr rfl fun i _ => by rw [hw₈]; ring
    rw [hsum7] at hz_eq
    linear_combination hz_eq
  have hz7 : z 7 ≠ 0 := by
    intro hz7_0
    have hz'_eq : weightedSumSquares F w (fun i : Fin 7 => z i.castSucc) = 0 := by
      simp only [weightedSumSquares_apply, smul_eq_mul]
      have hsum7' : ∑ x : Fin 7, w x * (z x.castSucc * z x.castSucc) =
          ∑ i : Fin 7, w i * z i.castSucc ^ 2 :=
        Finset.sum_congr rfl fun i _ => by ring
      rw [hsum7']
      rw [hz7_0] at hz_sum
      linear_combination hz_sum
    have hz'_0 := hQ0 _ hz'_eq
    apply hz_ne
    funext i
    fin_cases i
    · exact congr_fun hz'_0 0
    · exact congr_fun hz'_0 1
    · exact congr_fun hz'_0 2
    · exact congr_fun hz'_0 3
    · exact congr_fun hz'_0 4
    · exact congr_fun hz'_0 5
    · exact congr_fun hz'_0 6
    · exact hz7_0
  let v₀ : Fin 7 → F := fun i => z i.castSucc / z 7
  have hv₀ : weightedSumSquares F w v₀ = -d := by
    simp only [weightedSumSquares_apply, smul_eq_mul, v₀]
    have hmul : (∑ i : Fin 7, w i * (z i.castSucc / z 7 * (z i.castSucc / z 7))) * z 7 ^ 2 =
        ∑ i : Fin 7, w i * z i.castSucc ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp [hz7]
    have hnum : ∑ i : Fin 7, w i * z i.castSucc ^ 2 = (-d) * z 7 ^ 2 := by
      linear_combination hz_sum
    exact mul_right_cancel₀ (pow_ne_zero 2 hz7) (hmul.trans hnum)
  -- Step 3: Split off the orthogonal complement W of v₀ and compute det
  let φ : (Fin 7 → F) →ₗ[F] F :=
    { toFun := fun x => ∑ i : Fin 7, w i * v₀ i * x i
      map_add' := fun x y => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun a x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring }
  have hφv₀ : φ v₀ = -d := by
    have : φ v₀ = weightedSumSquares F w v₀ := by
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, weightedSumSquares_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [this, hv₀]
  have hφ_surj : Function.Surjective φ := by
    intro c
    refine ⟨(c / (-d)) • v₀, ?_⟩
    rw [map_smul, smul_eq_mul, hφv₀, div_mul_cancel₀ _ (neg_ne_zero.mpr hd)]
  let W : Submodule F (Fin 7 → F) := LinearMap.ker φ
  have hW_rank : Module.finrank F W = 6 := by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    have hr : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hφ_surj
    rw [hr, finrank_top, Module.finrank_self] at h
    have h7 : Module.finrank F (Fin 7 → F) = 7 := by simp
    rw [h7] at h
    change 1 + Module.finrank F W = 7 at h
    omega
  have hQ_orth : ∀ t : F, ∀ y ∈ W,
      weightedSumSquares F w (t • v₀ + y) = (-d) * t ^ 2 + weightedSumSquares F w y := by
    intro t y hy
    have hcross : ∑ i : Fin 7, w i * v₀ i * y i = 0 := LinearMap.mem_ker.mp hy
    have hsum : weightedSumSquares F w (t • v₀ + y) =
        t ^ 2 * weightedSumSquares F w v₀ +
        2 * t * (∑ i : Fin 7, w i * v₀ i * y i) +
        weightedSumSquares F w y := by
      simp only [weightedSumSquares_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hsum, hv₀, hcross]; ring
  let Q_W : QuadraticForm F W := (weightedSumSquares F w).comp W.subtype
  obtain ⟨p, ⟨eW⟩⟩ := Q_W.equivalent_weightedSumSquares
  generalize Module.finrank F W = mW at p eW hW_rank
  subst hW_rank
  let E : (Fin 7 → F) →ₗ[F] (Fin 7 → F) :=
    { toFun := fun x => (x 0) • v₀ + W.subtype (eW.symm (fun j : Fin 6 => x j.succ))
      map_add' := fun x y => by
        simp only [Pi.add_apply, add_smul]
        have : (fun j : Fin 6 => x j.succ + y j.succ) =
            (fun j : Fin 6 => x j.succ) + (fun j : Fin 6 => y j.succ) := rfl
        rw [this, map_add, map_add]; abel
      map_smul' := fun a x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul]
        have : (fun j : Fin 6 => a * x j.succ) = a • (fun j : Fin 6 => x j.succ) := rfl
        rw [this, map_smul, map_smul] }
  let w₂ : Fin 7 → F := ![-d, p 0, p 1, p 2, p 3, p 4, p 5]
  have hQE : ∀ x : Fin 7 → F, weightedSumSquares F w (E x) = weightedSumSquares F w₂ x := by
    intro x
    have hmem : W.subtype (eW.symm (fun j : Fin 6 => x j.succ)) ∈ W :=
      (eW.symm (fun j : Fin 6 => x j.succ)).2
    have h1 := hQ_orth (x 0) _ hmem
    have h2 : weightedSumSquares F w (W.subtype (eW.symm (fun j : Fin 6 => x j.succ))) =
        weightedSumSquares F p (fun j : Fin 6 => x j.succ) := by
      change Q_W (eW.symm (fun j : Fin 6 => x j.succ)) = _
      exact eW.symm.map_app _
    have hw2_0 : w₂ 0 = -d := rfl
    have hw2_succ : ∀ j : Fin 6, w₂ j.succ = p j := fun j => by fin_cases j <;> rfl
    rw [show E x = (x 0) • v₀ + W.subtype (eW.symm (fun j : Fin 6 => x j.succ)) from rfl, h1, h2]
    simp only [weightedSumSquares_apply, Fin.sum_univ_succ, smul_eq_mul, hw2_0, hw2_succ]
    ring
  have hE_inj : Function.Injective E := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : weightedSumSquares F w (E x) = 0 := by rw [hx, map_zero]
    rw [hQE x] at h0
    have hmem : W.subtype (eW.symm (fun j : Fin 6 => x j.succ)) ∈ W :=
      (eW.symm (fun j : Fin 6 => x j.succ)).2
    have hφx : φ (E x) = (-d) * x 0 := by
      change φ ((x 0) • v₀ + W.subtype (eW.symm (fun j : Fin 6 => x j.succ))) = _
      rw [map_add, map_smul, smul_eq_mul, hφv₀, LinearMap.mem_ker.mp hmem, add_zero]
      ring
    rw [hx, map_zero] at hφx
    have hx0 : x 0 = 0 := (mul_eq_zero.mp hφx.symm).resolve_left (neg_ne_zero.mpr hd)
    have hwy : W.subtype (eW.symm (fun j : Fin 6 => x j.succ)) = 0 := by
      have : E x = (x 0) • v₀ + W.subtype (eW.symm (fun j : Fin 6 => x j.succ)) := rfl
      rw [hx0, zero_smul, zero_add] at this
      exact this.symm.trans hx
    have heW0 : eW.symm (fun j : Fin 6 => x j.succ) = 0 := Subtype.ext hwy
    have hxrest : (fun j : Fin 6 => x j.succ) = 0 := by
      have := congrArg eW heW0
      simpa using this
    funext i
    refine Fin.cases hx0 (fun j => congr_fun hxrest j) i
  have hE_bij : Function.Bijective E :=
    ⟨hE_inj, LinearMap.injective_iff_surjective.mp hE_inj⟩
  let eE : (Fin 7 → F) ≃ₗ[F] (Fin 7 → F) := LinearEquiv.ofBijective E hE_bij
  let M : Matrix (Fin 7) (Fin 7) F := LinearMap.toMatrix' E
  have hc₀ : M.det ≠ 0 := by
    have hM_mul : M * LinearMap.toMatrix' (eE.symm : (Fin 7 → F) →ₗ[F] (Fin 7 → F)) = 1 := by
      rw [← LinearMap.toMatrix'_mul]
      have hcomp : E.comp (eE.symm : (Fin 7 → F) →ₗ[F] (Fin 7 → F)) = LinearMap.id :=
        LinearMap.ext fun x => eE.apply_symm_apply x
      rw [show E * (eE.symm : (Fin 7 → F) →ₗ[F] (Fin 7 → F)) = LinearMap.id from hcomp,
        LinearMap.toMatrix'_id]
    have hdet_mul := congrArg Matrix.det hM_mul
    rw [Matrix.det_mul, Matrix.det_one] at hdet_mul
    exact left_ne_zero_of_mul_eq_one hdet_mul
  have hgram : M.transpose * Matrix.diagonal w * M = Matrix.diagonal w₂ := by
    have hpol : ∀ x y : Fin 7 → F,
        ∑ k : Fin 7, w k * E x k * E y k = ∑ k : Fin 7, w₂ k * x k * y k := by
      intro x y
      have hxy := hQE (x + y)
      have hx := hQE x
      have hy := hQE y
      have hdiff : weightedSumSquares F w (E (x + y)) -
          weightedSumSquares F w (E x) - weightedSumSquares F w (E y) =
          weightedSumSquares F w₂ (x + y) - weightedSumSquares F w₂ x -
          weightedSumSquares F w₂ y := by rw [hxy, hx, hy]
      have hL : weightedSumSquares F w (E (x + y)) -
          weightedSumSquares F w (E x) - weightedSumSquares F w (E y) =
          2 * ∑ k : Fin 7, w k * E x k * E y k := by
        rw [map_add]
        simp only [weightedSumSquares_apply, Pi.add_apply, smul_eq_mul, Finset.mul_sum]
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
      have hR : weightedSumSquares F w₂ (x + y) -
          weightedSumSquares F w₂ x - weightedSumSquares F w₂ y =
          2 * ∑ k : Fin 7, w₂ k * x k * y k := by
        simp only [weightedSumSquares_apply, Pi.add_apply, smul_eq_mul, Finset.mul_sum]
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [hL, hR] at hdiff
      exact mul_left_cancel₀ (NeZero.ne (2 : F)) hdiff
    ext i j
    have hij := hpol (Pi.single i (1 : F)) (Pi.single j (1 : F))
    have hM_col : ∀ a k : Fin 7, E (Pi.single a (1 : F)) k = M k a := by
      intro a k
      simp [M, LinearMap.toMatrix'_apply]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply]
    have hL' : (∑ x : Fin 7, (∑ x_1 : Fin 7, M x_1 i *
        (if x_1 = x then w x_1 else 0)) * M x j) =
        ∑ k : Fin 7, w k * E (Pi.single i (1 : F)) k * E (Pi.single j (1 : F)) k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single k (fun a _ ha => by simp [ha]) (fun hk => absurd (Finset.mem_univ k) hk)]
      simp only [ite_true, hM_col i k, hM_col j k]; ring
    have hR' : (if i = j then w₂ i else 0) =
        ∑ k : Fin 7, w₂ k * (Pi.single i (1 : F) : Fin 7 → F) k *
          (Pi.single j (1 : F) : Fin 7 → F) k := by
      rw [Finset.sum_eq_single i]
      · by_cases h : i = j <;> simp [h]
      · intro k _ hk; simp [Pi.single_apply, hk]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [hL', hR', hij]
  have hdet_gram := congrArg Matrix.det hgram
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
    Matrix.det_diagonal] at hdet_gram
  have hprod_w : (∏ i : Fin 7, w i) = d := rfl
  have hprod_w2 : (∏ i : Fin 7, w₂ i) = (-d) * (p 0 * p 1 * p 2 * p 3 * p 4 * p 5) := by
    simp [Fin.prod_univ_seven, w₂, mul_assoc]
  rw [hprod_w, hprod_w2] at hdet_gram
  set c₀ := M.det
  have hp_sq : p 0 * p 1 * p 2 * p 3 * p 4 * p 5 = -(c₀ ^ 2) := by
    have h1 : d * (p 0 * p 1 * p 2 * p 3 * p 4 * p 5) = d * (-(c₀ ^ 2)) := by
      linear_combination hdet_gram
    exact mul_left_cancel₀ hd h1
  -- Step 4: Rescale to anisotropic ⟨1, b₀, b₁, b₂, b₃, b₄, b₅⟩ with b₀...b₅ = -t²
  let b : Fin 6 → F := fun i => p i / (-d)
  set t : F := c₀ / d ^ 3
  have ht : t ≠ 0 := div_ne_zero hc₀ (pow_ne_zero 3 hd)
  have hb_prod : b 0 * b 1 * b 2 * b 3 * b 4 * b 5 = -(t ^ 2) := by
    simp only [b, t]
    have h6 : (-d) ^ 6 = d ^ 6 := by ring
    calc p 0 / (-d) * (p 1 / (-d)) * (p 2 / (-d)) * (p 3 / (-d)) * (p 4 / (-d)) * (p 5 / (-d))
        = (p 0 * p 1 * p 2 * p 3 * p 4 * p 5) / (-d) ^ 6 := by ring
      _ = -(c₀ ^ 2) / d ^ 6 := by rw [hp_sq, h6]
      _ = -((c₀ / d ^ 3) ^ 2) := by ring
  have hb_ne : ∀ i : Fin 6, b i ≠ 0 := by
    intro i hi
    have h0 : b 0 * b 1 * b 2 * b 3 * b 4 * b 5 = 0 := by
      fin_cases i
      · change b 0 = 0 at hi; simp [hi]
      · change b 1 = 0 at hi; simp [hi]
      · change b 2 = 0 at hi; simp [hi]
      · change b 3 = 0 at hi; simp [hi]
      · change b 4 = 0 at hi; simp [hi]
      · change b 5 = 0 at hi; simp [hi]
    rw [hb_prod] at h0
    exact neg_ne_zero.mpr (pow_ne_zero 2 ht) h0
  let γ : QuadraticForm F (Fin 6 → F) := weightedSumSquares F b
  have h1γ_aniso : ∀ (x₀ : F) (y : Fin 6 → F), x₀ ^ 2 + γ y = 0 → x₀ = 0 ∧ y = 0 := by
    intro x₀ y hxy
    let x : Fin 7 → F := Fin.cons x₀ y
    have hQx : weightedSumSquares F w (E x) = 0 := by
      rw [hQE x]
      have hrew : weightedSumSquares F w₂ x = (-d) * (x₀ ^ 2 + γ y) := by
        have hw2_0 : w₂ 0 = -d := rfl
        have hw2_succ : ∀ j : Fin 6, w₂ j.succ = p j := fun j => by fin_cases j <;> rfl
        rw [weightedSumSquares_apply, Fin.sum_univ_succ, weightedSumSquares_apply]
        simp only [smul_eq_mul, hw2_0, hw2_succ, x, b, Fin.cons_zero, Fin.cons_succ]
        rw [mul_add, Finset.mul_sum]
        congr 1
        · ring
        · refine Finset.sum_congr rfl fun j _ => ?_
          field_simp [neg_ne_zero.mpr hd]
      rw [hrew, hxy, mul_zero]
    have hx0 : x = 0 := hE_inj ((hQ0 _ hQx).trans (map_zero E).symm)
    refine ⟨by simpa [x] using congr_fun hx0 0, ?_⟩
    funext j
    simpa [x] using congr_fun hx0 j.succ
  -- Step 5: Decompose ⟨1, -1⟩ ⊥ γ ≅ ⟨1, -1⟩ ⊥ γ' via two 2-fold Pfister forms
  set s : F := b 0 * b 1 * b 2
  have hs : s ≠ 0 := mul_ne_zero (mul_ne_zero (hb_ne 0) (hb_ne 1)) (hb_ne 2)
  set u₁ : F := b 0 / s
  set v₁ : F := b 1 / s
  set u₂ : F := -(b 3 / s)
  set v₂ : F := -(b 4 / s)
  have hu₁ : u₁ ≠ 0 := div_ne_zero (hb_ne 0) hs
  have hv₁ : v₁ ≠ 0 := div_ne_zero (hb_ne 1) hs
  have hu₂ : u₂ ≠ 0 := neg_ne_zero.mpr (div_ne_zero (hb_ne 3) hs)
  have hv₂ : v₂ ≠ 0 := neg_ne_zero.mpr (div_ne_zero (hb_ne 4) hs)
  obtain ⟨p₁, hp₁⟩ := pf4_universal h8_iso hu₁ hv₁ s
  obtain ⟨p₂, hp₂⟩ := pf4_universal h8_iso hu₂ hv₂ s
  let L₁ : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F) := qmulEquiv u₁ v₁ s hs p₁ hp₁
  let L₂ : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F) := qmulEquiv u₂ v₂ s hs p₂ hp₂
  have hL₁ : ∀ x : Fin 4 → F, pf4 u₁ v₁ (L₁ x) = s * pf4 u₁ v₁ x := fun x => by
    show pf4 u₁ v₁ (qmul u₁ v₁ p₁ x) = s * pf4 u₁ v₁ x
    rw [pf4_qmul, hp₁]
  have hL₂ : ∀ x : Fin 4 → F, pf4 u₂ v₂ (L₂ x) = s * pf4 u₂ v₂ x := fun x => by
    show pf4 u₂ v₂ (qmul u₂ v₂ p₂ x) = s * pf4 u₂ v₂ x
    rw [pf4_qmul, hp₂]
  -- Explicit linear equivalence Φ : (F × F × (Fin 6 → F)) ≃ₗ[F] (F × F × (Fin 6 → F))
  -- taking `a² - c² + γ y` to `a'² - c'² + γ' y'`
  let b' : Fin 6 → F := ![u₁, v₁, u₁ * v₁, -u₂, -v₂, -(u₂ * v₂)]
  let γ' : QuadraticForm F (Fin 6 → F) := weightedSumSquares F b'
  -- Step 5a: Transform (t₁, t₂) with `t₁² - t₂²` into (r₁, r₂) with `s r₁² - s r₂²`
  let H_s : (F × F) ≃ₗ[F] (F × F) :=
    { toFun := fun p => ((s + 1) / (2 * s) * p.1 + (s - 1) / (2 * s) * p.2,
                         (s - 1) / (2 * s) * p.1 + (s + 1) / (2 * s) * p.2)
      map_add' := fun x y => by ext <;> simp <;> ring
      map_smul' := fun c x => by ext <;> simp <;> ring
      invFun := fun q => ((s + 1) / 2 * q.1 - (s - 1) / 2 * q.2,
                          -(s - 1) / 2 * q.1 + (s + 1) / 2 * q.2)
      left_inv := fun p => by
        ext <;> simp <;> field_simp [hs, NeZero.ne (2 : F)] <;> ring
      right_inv := fun q => by
        ext <;> simp <;> field_simp [hs, NeZero.ne (2 : F)] <;> ring }
  have hH_s : ∀ p : F × F, s * (H_s p).1 ^ 2 - s * (H_s p).2 ^ 2 = p.1 ^ 2 - p.2 ^ 2 := by
    intro p
    simp only [H_s, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    field_simp [hs, NeZero.ne (2 : F)]
    ring
  -- Step 5b: Scale coordinates to match s * pf4 u₁ v₁ and (-s) * pf4 u₂ v₂
  set k₁ : F := b 2
  set k₂ : F := t / (b 3 * b 4)
  have hk₁ : k₁ ≠ 0 := hb_ne 2
  have hk₂ : k₂ ≠ 0 := div_ne_zero ht (mul_ne_zero (hb_ne 3) (hb_ne 4))
  let hsplit_to : (F × (F × (Fin 6 → F))) ≃ₗ[F] ((Fin 4 → F) × (Fin 4 → F)) :=
    { toFun := fun p =>
        (![(H_s (p.1, p.2.1)).1, p.2.2 0, p.2.2 1, k₁ * p.2.2 2],
         ![(H_s (p.1, p.2.1)).2, p.2.2 3, p.2.2 4, k₂ * p.2.2 5])
      map_add' := fun x y => by
        ext i <;> fin_cases i <;> simp [H_s] <;> ring
      map_smul' := fun c x => by
        ext i <;> fin_cases i <;> simp [H_s] <;> ring
      invFun := fun q =>
        ((H_s.symm (q.1 0, q.2 0)).1,
         (H_s.symm (q.1 0, q.2 0)).2,
         ![q.1 1, q.1 2, k₁⁻¹ * q.1 3, q.2 1, q.2 2, k₂⁻¹ * q.2 3])
      left_inv := fun p => by
        ext
        · simp
        · simp
        · rename_i i
          fin_cases i <;> simp [hk₁, hk₂]
      right_inv := fun q => by
        ext i <;> fin_cases i <;> simp [hk₁, hk₂] }
  let hsplit_from : ((Fin 4 → F) × (Fin 4 → F)) ≃ₗ[F] (F × (F × (Fin 6 → F))) :=
    { toFun := fun q => (q.1 0, q.2 0, ![q.1 1, q.1 2, q.1 3, q.2 1, q.2 2, q.2 3])
      map_add' := fun x y => by
        ext
        · rfl
        · rfl
        · rename_i i; fin_cases i <;> rfl
      map_smul' := fun c x => by
        ext
        · rfl
        · rfl
        · rename_i i; fin_cases i <;> rfl
      invFun := fun p => (![p.1, p.2.2 0, p.2.2 1, p.2.2 2], ![p.2.1, p.2.2 3, p.2.2 4, p.2.2 5])
      left_inv := fun q => by ext i <;> fin_cases i <;> rfl
      right_inv := fun p => by
        ext
        · rfl
        · rfl
        · rename_i i; fin_cases i <;> rfl }
  let Φ : (F × (F × (Fin 6 → F))) ≃ₗ[F] (F × (F × (Fin 6 → F))) :=
    (hsplit_to.trans (L₁.prodCongr L₂)).trans hsplit_from
  have hΦ : ∀ p : F × (F × (Fin 6 → F)),
      1 * (Φ p).1 ^ 2 + ((-1) * (Φ p).2.1 ^ 2 + γ' (Φ p).2.2) =
        1 * p.1 ^ 2 + ((-1) * p.2.1 ^ 2 + γ p.2.2) := by
    intro p
    set q := hsplit_to p
    have hΦ_eq : Φ p = (L₁ q.1 0, L₂ q.2 0,
        ![L₁ q.1 1, L₁ q.1 2, L₁ q.1 3, L₂ q.2 1, L₂ q.2 2, L₂ q.2 3]) := rfl
    have hL : 1 * (Φ p).1 ^ 2 + ((-1) * (Φ p).2.1 ^ 2 + γ' (Φ p).2.2) =
        pf4 u₁ v₁ (L₁ q.1) - pf4 u₂ v₂ (L₂ q.2) := by
      rw [hΦ_eq]
      simp only [γ', weightedSumSquares_apply, Fin.sum_univ_six, smul_eq_mul, b', pf4,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
      have h5b : ![u₁, v₁, u₁ * v₁, -u₂, -v₂, -(u₂ * v₂)] 5 = -(u₂ * v₂) := rfl
      have h5q : ![L₁ q.1 1, L₁ q.1 2, L₁ q.1 3, L₂ q.2 1, L₂ q.2 2, L₂ q.2 3] 5 = L₂ q.2 3 := rfl
      rw [h5b, h5q]
      ring
    rw [hL, hL₁, hL₂]
    have hq1_eq : q.1 = ![(H_s (p.1, p.2.1)).1, p.2.2 0, p.2.2 1, k₁ * p.2.2 2] := rfl
    have hq2_eq : q.2 = ![(H_s (p.1, p.2.1)).2, p.2.2 3, p.2.2 4, k₂ * p.2.2 5] := rfl
    have hq1 : s * pf4 u₁ v₁ q.1 =
        s * (H_s (p.1, p.2.1)).1 ^ 2 + b 0 * p.2.2 0 ^ 2 + b 1 * p.2.2 1 ^ 2 + b 2 * p.2.2 2 ^ 2 := by
      rw [hq1_eq]
      simp only [pf4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, u₁, v₁, k₁, s]
      field_simp [hb_ne 0, hb_ne 1, hb_ne 2]
    have hq2 : s * pf4 u₂ v₂ q.2 =
        s * (H_s (p.1, p.2.1)).2 ^ 2 - b 3 * p.2.2 3 ^ 2 - b 4 * p.2.2 4 ^ 2 - b 5 * p.2.2 5 ^ 2 := by
      have hb5_eq : b 5 = -(t ^ 2) / (s * b 3 * b 4) := by
        rw [eq_div_iff (mul_ne_zero (mul_ne_zero hs (hb_ne 3)) (hb_ne 4))]
        simp only [s]
        linear_combination hb_prod
      rw [hq2_eq]
      simp only [pf4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, u₂, v₂, k₂]
      rw [hb5_eq]
      field_simp [hs, hb_ne 3, hb_ne 4]
      ring
    rw [hq1, hq2]
    have hHs := hH_s (p.1, p.2.1)
    have hγ : γ p.2.2 = b 0 * p.2.2 0 ^ 2 + b 1 * p.2.2 1 ^ 2 + b 2 * p.2.2 2 ^ 2 +
        b 3 * p.2.2 3 ^ 2 + b 4 * p.2.2 4 ^ 2 + b 5 * p.2.2 5 ^ 2 := by
      simp only [γ, weightedSumSquares_apply, Fin.sum_univ_six, smul_eq_mul]
      ring
    rw [hγ]
    linear_combination hHs
  -- Step 6: Cancel ⟨1⟩ then ⟨-1⟩ using Witt cancellation to get γ ≅ γ'
  let Q₁ : QuadraticForm F (F × (Fin 6 → F)) := ((-1 : F) • (QuadraticMap.sq (R := F))).prod γ
  let Q₂ : QuadraticForm F (F × (Fin 6 → F)) := ((-1 : F) • (QuadraticMap.sq (R := F))).prod γ'
  have hΦ' : ∀ p : F × (F × (Fin 6 → F)),
      1 * (Φ p).1 ^ 2 + Q₂ (Φ p).2 = 1 * p.1 ^ 2 + Q₁ p.2 := by
    intro p
    simpa [Q₁, Q₂, _root_.sq] using hΦ p
  obtain ⟨Φ₁, hΦ₁⟩ := witt_cancel_one Q₁ Q₂ 1 one_ne_zero Φ hΦ'
  have hΦ₁' : ∀ q : F × (Fin 6 → F),
      (-1 : F) * (Φ₁ q).1 ^ 2 + γ' (Φ₁ q).2 = (-1 : F) * q.1 ^ 2 + γ q.2 := by
    intro q
    simpa [Q₁, Q₂, _root_.sq] using hΦ₁ q
  obtain ⟨Eγ, hEγ⟩ := witt_cancel_one γ γ' (-1) (neg_ne_zero.mpr one_ne_zero) Φ₁ hΦ₁'
  -- Step 7: Use universality of pf4 u₁ v₁ to represent u₂, contradicting anisotropy of ⟨1⟩ ⊥ γ
  obtain ⟨x, hx⟩ := pf4_universal h8_iso hu₁ hv₁ u₂
  let y' : Fin 6 → F := ![x 1, x 2, x 3, 1, 0, 0]
  have hy'_ne : y' ≠ 0 := by
    intro h
    exact (one_ne_zero : (1 : F) ≠ 0) (by simpa [y'] using congr_fun h 3)
  let y : Fin 6 → F := Eγ.symm y'
  have hy_ne : y ≠ 0 := by
    intro hy0
    apply hy'_ne
    have := congrArg Eγ hy0
    simpa [y] using this
  have hγy : γ y = γ' y' := by
    have := hEγ y
    simpa [y] using this.symm
  have hzero : x 0 ^ 2 + γ y = 0 := by
    rw [hγy]
    simp only [γ', weightedSumSquares_apply, Fin.sum_univ_six, smul_eq_mul, b', y',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    have h5b : ![u₁, v₁, u₁ * v₁, -u₂, -v₂, -(u₂ * v₂)] 5 = -(u₂ * v₂) := rfl
    have h5y : ![x 1, x 2, x 3, 1, 0, 0] 5 = 0 := rfl
    rw [h5b, h5y]
    simp only [pf4] at hx
    linear_combination hx
  exact hy_ne (h1γ_aniso (x 0) y hzero).2
