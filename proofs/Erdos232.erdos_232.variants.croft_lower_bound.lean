import FormalConjectures.ErdosProblems.«232»

/-!
# Proof of Erdős Problem 232 (Croft lower bound)

We prove `0.22936 ≤ Erdos232.m₁` using Croft's tortoise construction (1967):
intersect the open disc `B(0, 1/2)` with an open regular hexagon of inradius
`h = 221 / 458` (chosen from the Pythagorean triple `221² + 60² = 229²`, so
`y₀ = √(1/4 - h²) = 30 / 229` is exact rational), and tile copies of this tortoise
at a regular hexagonal lattice of spacing `d = 1 + 2h = 450 / 229`.

Every two points in the same tortoise have distance `< 1`; any two points in distinct
tortoises have distance `> 1` (using the hexagon projection along the 6 shortest lattice
directions, and distance `> 2 - 1 = 1` for all farther lattice vectors).

Each of the 6 congruent circular caps cut off from `B(0, 1/2)` is bounded above using
the elementary algebraic inequality `√(1/4 - y²) ≤ 1/2 - y² - y⁴`, whose polynomial
integral over `[-y₀, y₀]` yields an exact rational upper bound `capUB`, giving
density `(π/4 - 6 * capUB) / (d² * √3 / 2) > 0.2293636 > 0.22936`.
-/

namespace OMA_Erdos232_Croft

open Filter MeasureTheory
open scoped EuclideanGeometry

private noncomputable def hC : ℝ := 221 / 458
private noncomputable def y₀ : ℝ := 30 / 229
private noncomputable def dC : ℝ := 450 / 229

private noncomputable def capUB : ℝ :=
  2 * y₀ * (1 / 2 - hC) - 2 / 3 * y₀ ^ 3 - 2 / 5 * y₀ ^ 5

private lemma sqrt3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
private lemma sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

private lemma hC_y₀_sq : hC ^ 2 + y₀ ^ 2 = 1 / 4 := by
  unfold hC y₀; norm_num

private lemma dC_eq : dC = 1 + 2 * hC := by
  unfold dC hC; norm_num

private lemma dC_pos : (0 : ℝ) < dC := by
  unfold dC; norm_num

private lemma hC_pos : (0 : ℝ) < hC := by
  unfold hC; norm_num

private lemma y₀_pos : (0 : ℝ) < y₀ := by
  unfold y₀; norm_num

private noncomputable def cellArea : ℝ := dC ^ 2 * Real.sqrt 3 / 2
private noncomputable def croftAreaLB : ℝ := Real.pi / 4 - 6 * capUB
private noncomputable def croftDensLB : ℝ := croftAreaLB / cellArea

private lemma cellArea_pos : 0 < cellArea := by
  unfold cellArea
  have := dC_pos
  have := sqrt3_pos
  positivity

private lemma croftAreaLB_pos : 0 < croftAreaLB := by
  unfold croftAreaLB capUB y₀ hC
  have hpi := Real.pi_gt_d6
  linarith

private lemma croftDensLB_ge : (0.22936 : ℝ) ≤ croftDensLB := by
  unfold croftDensLB
  rw [le_div_iff₀ cellArea_pos]
  have hpi : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hsq3 : Real.sqrt 3 < 1732051 / 1000000 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hnum : (0.22936 : ℝ) * (dC ^ 2 * (1732051 / 1000000) / 2) <
      (3.141592 : ℝ) / 4 - 6 * capUB := by
    unfold dC capUB y₀ hC
    norm_num
  have h1 : (0.22936 : ℝ) * cellArea < (0.22936 : ℝ) * (dC ^ 2 * (1732051 / 1000000) / 2) := by
    unfold cellArea
    have hd2 : (0 : ℝ) < dC ^ 2 := sq_pos_of_pos dC_pos
    nlinarith
  have h2 : (3.141592 : ℝ) / 4 - 6 * capUB < croftAreaLB := by
    unfold croftAreaLB
    linarith
  linarith

/- ## Hexagonal lattice of spacing `dC` -/

private noncomputable def latP (p : ℤ × ℤ) : ℝ² :=
  !₂[dC * (p.1 : ℝ) + (dC / 2) * (p.2 : ℝ), (dC * Real.sqrt 3 / 2) * (p.2 : ℝ)]

private lemma latP_zero (p : ℤ × ℤ) : latP p 0 = dC * (p.1 : ℝ) + (dC / 2) * (p.2 : ℝ) := rfl
private lemma latP_one (p : ℤ × ℤ) : latP p 1 = (dC * Real.sqrt 3 / 2) * (p.2 : ℝ) := rfl

private lemma int_sq_ge_one {z : ℤ} (hz : z ≠ 0) : (1 : ℤ) ≤ z ^ 2 := by
  have : 1 ≤ z ∨ z ≤ -1 := by omega
  rcases this with h | h <;> nlinarith

private lemma int_norm_sq_ge_one (a b : ℤ) (h : a ≠ 0 ∨ b ≠ 0) :
    (1 : ℤ) ≤ a ^ 2 + a * b + b ^ 2 := by
  have h4 : (4 : ℤ) * (a ^ 2 + a * b + b ^ 2) = (2 * a + b) ^ 2 + 3 * b ^ 2 := by ring
  have hpos : (4 : ℤ) ≤ (2 * a + b) ^ 2 + 3 * b ^ 2 := by
    by_cases hb : b = 0
    · subst hb
      rcases h with ha | hb'
      · have := int_sq_ge_one ha
        nlinarith
      · exact absurd rfl hb'
    · have hb2 : (1 : ℤ) ≤ b ^ 2 := int_sq_ge_one hb
      by_cases hm : 2 * a + b = 0
      · have ha0 : a ≠ 0 := by intro ha0; subst ha0; omega
        have ha2 : (1 : ℤ) ≤ a ^ 2 := int_sq_ge_one ha0
        have hba : b = -2 * a := by omega
        rw [hba]; nlinarith
      · have hm2 : (1 : ℤ) ≤ (2 * a + b) ^ 2 := int_sq_ge_one hm
        nlinarith
  omega

private lemma norm_sq_latP_sub (p q : ℤ × ℤ) :
    ‖latP p - latP q‖ ^ 2 =
      dC ^ 2 * (((p.1 - q.1 : ℤ) : ℝ) ^ 2 + ((p.1 - q.1 : ℤ) : ℝ) * ((p.2 - q.2 : ℤ) : ℝ) +
        ((p.2 - q.2 : ℤ) : ℝ) ^ 2) := by
  have h0 : (latP p - latP q) 0 =
      dC * ((p.1 - q.1 : ℤ) : ℝ) + (dC / 2) * ((p.2 - q.2 : ℤ) : ℝ) := by
    simp only [latP_zero, PiLp.sub_apply, Int.cast_sub]; ring
  have h1 : (latP p - latP q) 1 = (dC * Real.sqrt 3 / 2) * ((p.2 - q.2 : ℤ) : ℝ) := by
    simp only [latP_one, PiLp.sub_apply, Int.cast_sub]; ring
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, h0, h1]
  have hsq : Real.sqrt 3 ^ 2 = 3 := sqrt3_sq
  nlinarith [sq_nonneg dC, sq_nonneg ((p.2 - q.2 : ℤ) : ℝ)]

private lemma latP_sep (p q : ℤ × ℤ) (h : p ≠ q) : dC ≤ dist (latP p) (latP q) := by
  rw [dist_eq_norm]
  have hab : p.1 - q.1 ≠ 0 ∨ p.2 - q.2 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (Prod.ext (sub_eq_zero.mp hc.1) (sub_eq_zero.mp hc.2))
  have h1 : (1 : ℝ) ≤ ((p.1 - q.1 : ℤ) : ℝ) ^ 2 +
      ((p.1 - q.1 : ℤ) : ℝ) * ((p.2 - q.2 : ℤ) : ℝ) + ((p.2 - q.2 : ℤ) : ℝ) ^ 2 := by
    exact_mod_cast int_norm_sq_ge_one (p.1 - q.1) (p.2 - q.2) hab
  have hsq : dC ^ 2 ≤ ‖latP p - latP q‖ ^ 2 := by
    rw [norm_sq_latP_sub]
    nlinarith [sq_nonneg dC]
  nlinarith [norm_nonneg (latP p - latP q), dC_pos]

/- ## Fundamental boxes for `latP` -/

private noncomputable def latCell (p : ℤ × ℤ) : Set ℝ² :=
  {x : ℝ² |
    x 0 ∈ Set.Ico (dC * (p.1 : ℝ) + (dC / 2) * (p.2 : ℝ))
      (dC * (p.1 : ℝ) + (dC / 2) * (p.2 : ℝ) + dC) ∧
    x 1 ∈ Set.Ico ((dC * Real.sqrt 3 / 2) * (p.2 : ℝ))
      ((dC * Real.sqrt 3 / 2) * (p.2 : ℝ) + dC * Real.sqrt 3 / 2)}

private lemma volume_rect {l u l' u' : ℝ} :
    volume {x : ℝ² | x 0 ∈ Set.Ico l u ∧ x 1 ∈ Set.Ico l' u'} =
      ENNReal.ofReal (u - l) * ENNReal.ofReal (u' - l') := by
  have hmeas : NullMeasurableSet {x : ℝ² | x 0 ∈ Set.Ico l u ∧ x 1 ∈ Set.Ico l' u'} volume := by
    measurability
  rw [← (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage hmeas]
  have hpre : (WithLp.toLp 2 : (Fin 2 → ℝ) → ℝ²) ⁻¹'
      {x : ℝ² | x 0 ∈ Set.Ico l u ∧ x 1 ∈ Set.Ico l' u'} =
      Set.pi Set.univ
        (fun i : Fin 2 => Set.Ico ((![l, l'] : Fin 2 → ℝ) i) ((![u, u'] : Fin 2 → ℝ) i)) := by
    ext y
    simp [Set.mem_pi, Fin.forall_fin_two]
  rw [hpre, Real.volume_pi_Ico]
  simp [Fin.prod_univ_two]

private lemma latCell_volume (p : ℤ × ℤ) : volume (latCell p) = ENNReal.ofReal cellArea := by
  unfold latCell cellArea
  have h := volume_rect
    (l := dC * (p.1 : ℝ) + (dC / 2) * (p.2 : ℝ))
    (u := dC * (p.1 : ℝ) + (dC / 2) * (p.2 : ℝ) + dC)
    (l' := (dC * Real.sqrt 3 / 2) * (p.2 : ℝ))
    (u' := (dC * Real.sqrt 3 / 2) * (p.2 : ℝ) + dC * Real.sqrt 3 / 2)
  have e1 : dC * (p.1 : ℝ) + (dC / 2) * (p.2 : ℝ) + dC -
      (dC * (p.1 : ℝ) + (dC / 2) * (p.2 : ℝ)) = dC := by ring
  have e2 : (dC * Real.sqrt 3 / 2) * (p.2 : ℝ) + dC * Real.sqrt 3 / 2 -
      (dC * Real.sqrt 3 / 2) * (p.2 : ℝ) = dC * Real.sqrt 3 / 2 := by ring
  rw [e1, e2] at h
  rw [h, ← ENNReal.ofReal_mul dC_pos.le]
  congr 1; ring

private lemma latCell_cover (x : ℝ²) : ∃ p : ℤ × ℤ, x ∈ latCell p := by
  have hstep1 : 0 < dC * Real.sqrt 3 / 2 := by have := dC_pos; have := sqrt3_pos; positivity
  set b : ℤ := ⌊x 1 / (dC * Real.sqrt 3 / 2)⌋
  have hb1 : (b : ℝ) ≤ x 1 / (dC * Real.sqrt 3 / 2) := Int.floor_le _
  have hb2 : x 1 / (dC * Real.sqrt 3 / 2) < (b : ℝ) + 1 := Int.lt_floor_add_one _
  have hy1 : (dC * Real.sqrt 3 / 2) * (b : ℝ) ≤ x 1 := by
    have := mul_le_mul_of_nonneg_left hb1 hstep1.le
    rwa [mul_div_cancel₀ _ hstep1.ne'] at this
  have hy2 : x 1 < (dC * Real.sqrt 3 / 2) * (b : ℝ) + dC * Real.sqrt 3 / 2 := by
    have := mul_lt_mul_of_pos_left hb2 hstep1
    rw [mul_div_cancel₀ _ hstep1.ne', mul_add, mul_one] at this
    exact this
  set a : ℤ := ⌊(x 0 - (dC / 2) * (b : ℝ)) / dC⌋
  have ha1 : (a : ℝ) ≤ (x 0 - (dC / 2) * (b : ℝ)) / dC := Int.floor_le _
  have ha2 : (x 0 - (dC / 2) * (b : ℝ)) / dC < (a : ℝ) + 1 := Int.lt_floor_add_one _
  have hx1 : dC * (a : ℝ) + (dC / 2) * (b : ℝ) ≤ x 0 := by
    have := mul_le_mul_of_nonneg_left ha1 dC_pos.le
    rw [mul_div_cancel₀ _ dC_pos.ne'] at this
    linarith
  have hx2 : x 0 < dC * (a : ℝ) + (dC / 2) * (b : ℝ) + dC := by
    have := mul_lt_mul_of_pos_left ha2 dC_pos
    rw [mul_div_cancel₀ _ dC_pos.ne', mul_add, mul_one] at this
    linarith
  exact ⟨(a, b), ⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩

private lemma norm_sub_latP_lt_three (p : ℤ × ℤ) {x : ℝ²} (hx : x ∈ latCell p) :
    ‖x - latP p‖ < 3 := by
  have hsq : ‖x - latP p‖ ^ 2 < 9 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    have e0 : (x - latP p) 0 = x 0 - (dC * (p.1 : ℝ) + (dC / 2) * (p.2 : ℝ)) := by
      simp only [latP_zero, PiLp.sub_apply]
    have e1 : (x - latP p) 1 = x 1 - (dC * Real.sqrt 3 / 2) * (p.2 : ℝ) := by
      simp only [latP_one, PiLp.sub_apply]
    rw [e0, e1]
    have hn0 : 0 ≤ x 0 - (dC * (p.1 : ℝ) + (dC / 2) * (p.2 : ℝ)) := by linarith [hx.1.1]
    have hn0' : x 0 - (dC * (p.1 : ℝ) + (dC / 2) * (p.2 : ℝ)) < dC := by linarith [hx.1.2]
    have hn1 : 0 ≤ x 1 - (dC * Real.sqrt 3 / 2) * (p.2 : ℝ) := by linarith [hx.2.1]
    have hn1' : x 1 - (dC * Real.sqrt 3 / 2) * (p.2 : ℝ) < dC * Real.sqrt 3 / 2 := by
      linarith [hx.2.2]
    have hdC2 : dC ^ 2 < 4 := by unfold dC; norm_num
    nlinarith [sqrt3_sq]
  nlinarith [norm_nonneg (x - latP p)]

private lemma latP_finite (M : ℝ) : {p : ℤ × ℤ | ‖latP p‖ ≤ M}.Finite := by
  by_cases hM : M < 0
  · have : {p : ℤ × ℤ | ‖latP p‖ ≤ M} = ∅ := by
      ext p; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hp; linarith [norm_nonneg (latP p)]
    rw [this]; exact Set.finite_empty
  push Not at hM
  set k : ℤ := ⌈2 * M / dC⌉ + 1
  have hkM : 2 * M / dC ≤ (k : ℝ) := by
    have := Int.le_ceil (2 * M / dC)
    push_cast [k]; linarith
  refine Set.Finite.subset (Set.Finite.prod (Set.finite_Icc (-k) k) (Set.finite_Icc (-k) k)) ?_
  intro p hp
  have hp' : ‖latP p‖ ≤ M := hp
  simp only [Set.mem_prod, Set.mem_Icc]
  have hsq : ‖latP p‖ ^ 2 =
      (dC * (p.1 : ℝ) + (dC / 2) * (p.2 : ℝ)) ^ 2 + (dC * Real.sqrt 3 / 2 * (p.2 : ℝ)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, latP_zero, latP_one]
  have hM2 : ‖latP p‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg (latP p)]
  have hb_sq : (dC * (p.2 : ℝ)) ^ 2 ≤ (2 * M) ^ 2 := by
    have h1 : (dC * Real.sqrt 3 / 2 * (p.2 : ℝ)) ^ 2 ≤ M ^ 2 := by
      nlinarith [sq_nonneg (dC * (p.1 : ℝ) + (dC / 2) * (p.2 : ℝ))]
    have h2 : (dC * Real.sqrt 3 / 2 * (p.2 : ℝ)) ^ 2 = 3 / 4 * (dC * (p.2 : ℝ)) ^ 2 := by
      have := sqrt3_sq; ring_nf; nlinarith
    nlinarith
  have hab_sq : (dC * (p.1 : ℝ) + (dC / 2) * (p.2 : ℝ)) ^ 2 ≤ M ^ 2 := by
    nlinarith [sq_nonneg (dC * Real.sqrt 3 / 2 * (p.2 : ℝ))]
  have hb_abs : |(p.2 : ℝ)| ≤ 2 * M / dC := by
    rw [le_div_iff₀ dC_pos, ← abs_of_pos dC_pos, ← abs_mul, mul_comm]
    have := sq_le_sq.mp hb_sq
    rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * M)] at this
  have hab_abs : |dC * (p.1 : ℝ) + (dC / 2) * (p.2 : ℝ)| ≤ M := by
    have := sq_le_sq.mp hab_sq
    rwa [abs_of_nonneg hM] at this
  have ha_abs : |(p.1 : ℝ)| ≤ 2 * M / dC := by
    rw [le_div_iff₀ dC_pos, ← abs_of_pos dC_pos, ← abs_mul, mul_comm]
    have hsplit : dC * (p.1 : ℝ) =
        (dC * (p.1 : ℝ) + (dC / 2) * (p.2 : ℝ)) - (dC / 2) * (p.2 : ℝ) := by ring
    rw [hsplit]
    have htri := abs_sub (dC * (p.1 : ℝ) + (dC / 2) * (p.2 : ℝ)) ((dC / 2) * (p.2 : ℝ))
    have hb2 : |(dC / 2) * (p.2 : ℝ)| ≤ M := by
      rw [abs_mul, abs_of_pos (by linarith [dC_pos] : (0 : ℝ) < dC / 2)]
      have h' : |(p.2 : ℝ)| * dC ≤ 2 * M := (le_div_iff₀ dC_pos).mp hb_abs
      linarith
    linarith
  have to_icc : ∀ n : ℤ, |(n : ℝ)| ≤ (k : ℝ) → -k ≤ n ∧ n ≤ k := by
    intro n hn
    obtain ⟨h1, h2⟩ := abs_le.mp hn
    exact ⟨by exact_mod_cast (by push_cast; linarith : ((-k : ℤ) : ℝ) ≤ (n : ℝ)),
      by exact_mod_cast h2⟩
  exact ⟨to_icc p.1 (ha_abs.trans hkM), to_icc p.2 (hb_abs.trans hkM)⟩

/- ## Croft's tortoise and unit-distance avoidance -/

private noncomputable def tortoise : Set ℝ² :=
  {x : ℝ² | ‖x‖ < 1 / 2 ∧
    |x 0| < hC ∧
    |x 0 / 2 + Real.sqrt 3 / 2 * x 1| < hC ∧
    |-(x 0 / 2) + Real.sqrt 3 / 2 * x 1| < hC}

private noncomputable def tortoiseAt (p : ℤ × ℤ) : Set ℝ² :=
  (fun x : ℝ² => x + (-latP p)) ⁻¹' tortoise

private noncomputable def croftSet : Set ℝ² :=
  ⋃ p : ℤ × ℤ, tortoiseAt p

private lemma tortoise_isOpen : IsOpen tortoise := by
  have h0 : Continuous (fun x : ℝ² => x 0) := PiLp.continuous_apply 2 (fun _ => ℝ) 0
  have h1 : Continuous (fun x : ℝ² => x 1) := PiLp.continuous_apply 2 (fun _ => ℝ) 1
  have hc1 : IsOpen {x : ℝ² | ‖x‖ < 1 / 2} := isOpen_lt continuous_norm continuous_const
  have hc2 : IsOpen {x : ℝ² | |x 0| < hC} := isOpen_lt (continuous_abs.comp h0) continuous_const
  have hc3 : IsOpen {x : ℝ² | |x 0 / 2 + Real.sqrt 3 / 2 * x 1| < hC} :=
    isOpen_lt (continuous_abs.comp ((h0.div_const 2).add (continuous_const.mul h1))) continuous_const
  have hc4 : IsOpen {x : ℝ² | |-(x 0 / 2) + Real.sqrt 3 / 2 * x 1| < hC} :=
    isOpen_lt (continuous_abs.comp ((h0.div_const 2).neg.add (continuous_const.mul h1)))
      continuous_const
  exact hc1.inter (hc2.inter (hc3.inter hc4))

private lemma tortoiseAt_isOpen (p : ℤ × ℤ) : IsOpen (tortoiseAt p) :=
  tortoise_isOpen.preimage (continuous_id.add continuous_const)

private lemma croftSet_nullMeasurable : NullMeasurableSet croftSet volume :=
  (isOpen_iUnion tortoiseAt_isOpen).measurableSet.nullMeasurableSet

private lemma tortoiseAt_volume (p : ℤ × ℤ) : volume (tortoiseAt p) = volume tortoise :=
  (MeasureTheory.measurePreserving_add_right volume (-latP p)).measure_preimage
    tortoise_isOpen.measurableSet.nullMeasurableSet

private lemma tortoiseAt_subset_ball (p : ℤ × ℤ) : tortoiseAt p ⊆ Metric.ball (latP p) (1 / 2) := by
  intro x hx
  rw [Metric.mem_ball, dist_eq_norm]
  have hnorm : ‖x + (-latP p)‖ < 1 / 2 := hx.1
  simpa [sub_eq_add_neg] using hnorm

private lemma tortoiseAt_disjoint (p q : ℤ × ℤ) (h : p ≠ q) :
    Disjoint (tortoiseAt p) (tortoiseAt q) := by
  rw [Set.disjoint_left]
  intro x hxp hxq
  have hp := Metric.mem_ball.mp (tortoiseAt_subset_ball p hxp)
  have hq := Metric.mem_ball.mp (tortoiseAt_subset_ball q hxq)
  have hsep := latP_sep p q h
  have htri : dist (latP p) (latP q) ≤ dist (latP p) x + dist x (latP q) := dist_triangle _ _ _
  rw [dist_comm (latP p) x] at htri
  have hd1 : (1 : ℝ) < dC := by unfold dC; norm_num
  linarith

private lemma abs_L1_le_norm (z : ℝ²) : |z 0| ≤ ‖z‖ := by
  have hsq : |z 0| ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [sq_abs, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    nlinarith [sq_nonneg (z 1)]
  nlinarith [norm_nonneg z, abs_nonneg (z 0)]

private lemma abs_L2_le_norm (z : ℝ²) : |z 0 / 2 + Real.sqrt 3 / 2 * z 1| ≤ ‖z‖ := by
  have hsq : |z 0 / 2 + Real.sqrt 3 / 2 * z 1| ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [sq_abs, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    have h3 : Real.sqrt 3 ^ 2 = 3 := sqrt3_sq
    nlinarith [sq_nonneg (-(Real.sqrt 3 / 2) * z 0 + z 1 / 2)]
  nlinarith [norm_nonneg z, abs_nonneg (z 0 / 2 + Real.sqrt 3 / 2 * z 1)]

private lemma abs_L3_le_norm (z : ℝ²) : |-(z 0 / 2) + Real.sqrt 3 / 2 * z 1| ≤ ‖z‖ := by
  have hsq : |-(z 0 / 2) + Real.sqrt 3 / 2 * z 1| ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [sq_abs, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    have h3 : Real.sqrt 3 ^ 2 = 3 := sqrt3_sq
    nlinarith [sq_nonneg (-(Real.sqrt 3 / 2) * z 0 - z 1 / 2)]
  nlinarith [norm_nonneg z, abs_nonneg (-(z 0 / 2) + Real.sqrt 3 / 2 * z 1)]

private lemma croftSet_unitDistanceAvoiding : Erdos214.UnitDistanceAvoiding croftSet := by
  intro x hx y hy
  rcases Set.mem_iUnion.mp hx with ⟨p, hxp⟩
  rcases Set.mem_iUnion.mp hy with ⟨q, hyq⟩
  set x' : ℝ² := x + (-latP p)
  set y' : ℝ² := y + (-latP q)
  have hx' : x' ∈ tortoise := hxp
  have hy' : y' ∈ tortoise := hyq
  have hxy_decomp : x - y = (latP p - latP q) + x' - y' := by
    ext i; simp only [x', y', PiLp.sub_apply, PiLp.add_apply, PiLp.neg_apply]; ring
  rcases eq_or_ne p q with rfl | hpq
  · have hlt : dist x y < 1 := by
      rw [dist_eq_norm, hxy_decomp, sub_self, zero_add]
      calc ‖x' - y'‖ ≤ ‖x'‖ + ‖y'‖ := norm_sub_le _ _
        _ < 1 / 2 + 1 / 2 := add_lt_add hx'.1 hy'.1
        _ = 1 := by norm_num
    exact ne_of_lt hlt
  · set a : ℤ := p.1 - q.1
    set b : ℤ := p.2 - q.2
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra hc; push Not at hc
      exact hpq (Prod.ext (sub_eq_zero.mp hc.1) (sub_eq_zero.mp hc.2))
    have hN1 : (1 : ℤ) ≤ a ^ 2 + a * b + b ^ 2 := int_norm_sq_ge_one a b hab
    by_cases hN_eq1 : a ^ 2 + a * b + b ^ 2 = 1
    · have h4 : (2 * a + b) ^ 2 + 3 * b ^ 2 = 4 := by nlinarith
      have hb_cases : b = -1 ∨ b = 0 ∨ b = 1 := by
        have : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg (2 * a + b)]
        have h1 : -1 ≤ b := by nlinarith
        have h2 : b ≤ 1 := by nlinarith
        omega
      have hgt : 1 < dist x y := by
        rw [dist_eq_norm]
        rcases hb_cases with hb | hb | hb
        · have ha_cases : a = 0 ∨ a = 1 := by
            rw [hb] at h4
            have hfac : (2 * a) * (2 * a - 2) = 0 := by linarith
            rcases mul_eq_zero.mp hfac with h | h <;> [left; right] <;> omega
          rcases ha_cases with ha | ha
          · -- (a, b) = (0, -1): latP p - latP q = (-dC/2, -dC*√3/2)
            have hL : (x - y) 0 / 2 + Real.sqrt 3 / 2 * (x - y) 1 =
                -dC + (x' 0 / 2 + Real.sqrt 3 / 2 * x' 1) -
                (y' 0 / 2 + Real.sqrt 3 / 2 * y' 1) := by
              rw [hxy_decomp]
              simp only [PiLp.sub_apply, PiLp.add_apply, latP_zero, latP_one]
              have hp1 : (p.1 : ℝ) = (q.1 : ℝ) := by
                have : (p.1 : ℝ) - (q.1 : ℝ) = 0 := by exact_mod_cast ha
                linarith
              have hp2 : (p.2 : ℝ) = (q.2 : ℝ) - 1 := by
                have : (p.2 : ℝ) - (q.2 : ℝ) = -1 := by exact_mod_cast hb
                linarith
              rw [hp1, hp2]; ring_nf; rw [sqrt3_sq]; ring
            have habs : 1 < |(x - y) 0 / 2 + Real.sqrt 3 / 2 * (x - y) 1| := by
              rw [hL]
              have hx2 := (abs_lt.mp hx'.2.2.1).2
              have hy2 := (abs_lt.mp hy'.2.2.1).1
              have hd := dC_eq
              have hneg : -dC + (x' 0 / 2 + Real.sqrt 3 / 2 * x' 1) -
                  (y' 0 / 2 + Real.sqrt 3 / 2 * y' 1) < -1 := by linarith
              rw [abs_of_neg (by linarith)]; linarith
            exact lt_of_lt_of_le habs (abs_L2_le_norm (x - y))
          · -- (a, b) = (1, -1): latP p - latP q = (dC/2, -dC*√3/2)
            have hL : -((x - y) 0 / 2) + Real.sqrt 3 / 2 * (x - y) 1 =
                -dC + (-(x' 0 / 2) + Real.sqrt 3 / 2 * x' 1) -
                (-(y' 0 / 2) + Real.sqrt 3 / 2 * y' 1) := by
              rw [hxy_decomp]
              simp only [PiLp.sub_apply, PiLp.add_apply, latP_zero, latP_one]
              have hp1 : (p.1 : ℝ) = (q.1 : ℝ) + 1 := by
                have : (p.1 : ℝ) - (q.1 : ℝ) = 1 := by exact_mod_cast ha
                linarith
              have hp2 : (p.2 : ℝ) = (q.2 : ℝ) - 1 := by
                have : (p.2 : ℝ) - (q.2 : ℝ) = -1 := by exact_mod_cast hb
                linarith
              rw [hp1, hp2]; ring_nf; rw [sqrt3_sq]; ring
            have habs : 1 < |-((x - y) 0 / 2) + Real.sqrt 3 / 2 * (x - y) 1| := by
              rw [hL]
              have hx3 := (abs_lt.mp hx'.2.2.2).2
              have hy3 := (abs_lt.mp hy'.2.2.2).1
              have hd := dC_eq
              have hneg : -dC + (-(x' 0 / 2) + Real.sqrt 3 / 2 * x' 1) -
                  (-(y' 0 / 2) + Real.sqrt 3 / 2 * y' 1) < -1 := by linarith
              rw [abs_of_neg (by linarith)]; linarith
            exact lt_of_lt_of_le habs (abs_L3_le_norm (x - y))
        · have ha_cases : a = -1 ∨ a = 1 := by
            rw [hb] at h4
            have hfac : (a + 1) * (a - 1) = 0 := by linarith
            rcases mul_eq_zero.mp hfac with h | h <;> [left; right] <;> omega
          rcases ha_cases with ha | ha
          · -- (a, b) = (-1, 0)
            have hL : (x - y) 0 = -dC + x' 0 - y' 0 := by
              rw [hxy_decomp]
              simp only [PiLp.sub_apply, PiLp.add_apply, latP_zero]
              have hp1 : (p.1 : ℝ) = (q.1 : ℝ) - 1 := by
                have : (p.1 : ℝ) - (q.1 : ℝ) = -1 := by exact_mod_cast ha
                linarith
              have hp2 : (p.2 : ℝ) = (q.2 : ℝ) := by
                have : (p.2 : ℝ) - (q.2 : ℝ) = 0 := by exact_mod_cast hb
                linarith
              rw [hp1, hp2]; ring
            have habs : 1 < |(x - y) 0| := by
              rw [hL]
              have hx1 := (abs_lt.mp hx'.2.1).2
              have hy1 := (abs_lt.mp hy'.2.1).1
              have hd := dC_eq
              rw [abs_of_neg (by linarith)]; linarith
            exact lt_of_lt_of_le habs (abs_L1_le_norm (x - y))
          · -- (a, b) = (1, 0)
            have hL : (x - y) 0 = dC + x' 0 - y' 0 := by
              rw [hxy_decomp]
              simp only [PiLp.sub_apply, PiLp.add_apply, latP_zero]
              have hp1 : (p.1 : ℝ) = (q.1 : ℝ) + 1 := by
                have : (p.1 : ℝ) - (q.1 : ℝ) = 1 := by exact_mod_cast ha
                linarith
              have hp2 : (p.2 : ℝ) = (q.2 : ℝ) := by
                have : (p.2 : ℝ) - (q.2 : ℝ) = 0 := by exact_mod_cast hb
                linarith
              rw [hp1, hp2]; ring
            have habs : 1 < |(x - y) 0| := by
              rw [hL]
              have hx1 := (abs_lt.mp hx'.2.1).1
              have hy1 := (abs_lt.mp hy'.2.1).2
              have hd := dC_eq
              rw [abs_of_pos (by linarith)]; linarith
            exact lt_of_lt_of_le habs (abs_L1_le_norm (x - y))
        · have ha_cases : a = 0 ∨ a = -1 := by
            rw [hb] at h4
            have hfac : (2 * a) * (2 * a + 2) = 0 := by linarith
            rcases mul_eq_zero.mp hfac with h | h <;> [left; right] <;> omega
          rcases ha_cases with ha | ha
          · -- (a, b) = (0, 1)
            have hL : (x - y) 0 / 2 + Real.sqrt 3 / 2 * (x - y) 1 =
                dC + (x' 0 / 2 + Real.sqrt 3 / 2 * x' 1) -
                (y' 0 / 2 + Real.sqrt 3 / 2 * y' 1) := by
              rw [hxy_decomp]
              simp only [PiLp.sub_apply, PiLp.add_apply, latP_zero, latP_one]
              have hp1 : (p.1 : ℝ) = (q.1 : ℝ) := by
                have : (p.1 : ℝ) - (q.1 : ℝ) = 0 := by exact_mod_cast ha
                linarith
              have hp2 : (p.2 : ℝ) = (q.2 : ℝ) + 1 := by
                have : (p.2 : ℝ) - (q.2 : ℝ) = 1 := by exact_mod_cast hb
                linarith
              rw [hp1, hp2]; ring_nf; rw [sqrt3_sq]; ring
            have habs : 1 < |(x - y) 0 / 2 + Real.sqrt 3 / 2 * (x - y) 1| := by
              rw [hL]
              have hx2 := (abs_lt.mp hx'.2.2.1).1
              have hy2 := (abs_lt.mp hy'.2.2.1).2
              have hd := dC_eq
              rw [abs_of_pos (by linarith)]; linarith
            exact lt_of_lt_of_le habs (abs_L2_le_norm (x - y))
          · -- (a, b) = (-1, 1)
            have hL : -((x - y) 0 / 2) + Real.sqrt 3 / 2 * (x - y) 1 =
                dC + (-(x' 0 / 2) + Real.sqrt 3 / 2 * x' 1) -
                (-(y' 0 / 2) + Real.sqrt 3 / 2 * y' 1) := by
              rw [hxy_decomp]
              simp only [PiLp.sub_apply, PiLp.add_apply, latP_zero, latP_one]
              have hp1 : (p.1 : ℝ) = (q.1 : ℝ) - 1 := by
                have : (p.1 : ℝ) - (q.1 : ℝ) = -1 := by exact_mod_cast ha
                linarith
              have hp2 : (p.2 : ℝ) = (q.2 : ℝ) + 1 := by
                have : (p.2 : ℝ) - (q.2 : ℝ) = 1 := by exact_mod_cast hb
                linarith
              rw [hp1, hp2]; ring_nf; rw [sqrt3_sq]; ring
            have habs : 1 < |-((x - y) 0 / 2) + Real.sqrt 3 / 2 * (x - y) 1| := by
              rw [hL]
              have hx3 := (abs_lt.mp hx'.2.2.2).1
              have hy3 := (abs_lt.mp hy'.2.2.2).2
              have hd := dC_eq
              rw [abs_of_pos (by linarith)]; linarith
            exact lt_of_lt_of_le habs (abs_L3_le_norm (x - y))
      exact ne_of_gt hgt
    · -- a² + ab + b² ≥ 2 ⇒ ‖latP p - latP q‖ > 2
      have hN2 : (2 : ℝ) ≤ (a : ℝ) ^ 2 + (a : ℝ) * (b : ℝ) + (b : ℝ) ^ 2 := by
        have : (2 : ℤ) ≤ a ^ 2 + a * b + b ^ 2 := by omega
        exact_mod_cast this
      have hdist_gt2 : 2 < ‖latP p - latP q‖ := by
        have hsq : (4 : ℝ) < ‖latP p - latP q‖ ^ 2 := by
          rw [norm_sq_latP_sub]
          have hd2 : (4 : ℝ) < 2 * dC ^ 2 := by unfold dC; norm_num
          nlinarith [sq_nonneg dC]
        nlinarith [norm_nonneg (latP p - latP q)]
      have hgt : 1 < dist x y := by
        rw [dist_eq_norm]
        have htri : ‖latP p - latP q‖ ≤ ‖x - y‖ + ‖x'‖ + ‖y'‖ := by
          have h1 : latP p - latP q = (x - y) - x' + y' := by
            ext i; simp only [x', y', PiLp.sub_apply, PiLp.add_apply, PiLp.neg_apply]; ring
          rw [h1]
          calc ‖(x - y) - x' + y'‖ ≤ ‖(x - y) - x'‖ + ‖y'‖ := norm_add_le _ _
            _ ≤ ‖x - y‖ + ‖x'‖ + ‖y'‖ := by linarith [norm_sub_le (x - y) x']
        linarith [hx'.1, hy'.1]
      exact ne_of_gt hgt

/- ## Area lower bound for the Croft tortoise -/

private noncomputable def mkOrtho (a b c e : ℝ)
    (h1 : a ^ 2 + c ^ 2 = 1) (h2 : b ^ 2 + e ^ 2 = 1) (h3 : a * b + c * e = 0)
    (h4 : a ^ 2 + b ^ 2 = 1) (h5 : c ^ 2 + e ^ 2 = 1) (h6 : a * c + b * e = 0) :
    ℝ² ≃ₗᵢ[ℝ] ℝ² :=
  { toFun := fun x => !₂[a * x 0 + b * x 1, c * x 0 + e * x 1]
    map_add' := fun x y => by ext i; fin_cases i <;> simp <;> ring
    map_smul' := fun r x => by ext i; fin_cases i <;> simp <;> ring
    invFun := fun y => !₂[a * y 0 + c * y 1, b * y 0 + e * y 1]
    left_inv := fun x => by
      ext i; fin_cases i
      · simp; linear_combination x 0 * h1 + x 1 * h3
      · simp; linear_combination x 0 * h3 + x 1 * h2
    right_inv := fun y => by
      ext i; fin_cases i
      · simp; linear_combination y 0 * h4 + y 1 * h6
      · simp; linear_combination y 0 * h6 + y 1 * h5
    norm_map' := fun x => by
      change ‖(!₂[a * x 0 + b * x 1, c * x 0 + e * x 1] : ℝ²)‖ = ‖x‖
      have hsq : ‖(!₂[a * x 0 + b * x 1, c * x 0 + e * x 1] : ℝ²)‖ ^ 2 = ‖x‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
          Fin.sum_univ_two, Fin.sum_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        linear_combination (x 0) ^ 2 * h1 + (x 1) ^ 2 * h2 + 2 * x 0 * x 1 * h3
      nlinarith [norm_nonneg (!₂[a * x 0 + b * x 1, c * x 0 + e * x 1] : ℝ²), norm_nonneg x] }

private noncomputable def cap0 : Set ℝ² :=
  {x : ℝ² | ‖x‖ < 1 / 2 ∧ hC ≤ x 0}

private lemma cap0_measurable : MeasurableSet cap0 := by
  have h0 : Continuous (fun x : ℝ² => x 0) := PiLp.continuous_apply 2 (fun _ => ℝ) 0
  have h1 : MeasurableSet {x : ℝ² | ‖x‖ < 1 / 2} :=
    (isOpen_lt continuous_norm continuous_const).measurableSet
  have h2 : MeasurableSet {x : ℝ² | hC ≤ x 0} :=
    (isClosed_le continuous_const h0).measurableSet
  exact h1.inter h2

private lemma cap0_volume_le : volume cap0 ≤ ENNReal.ofReal capUB := by
  let toLp2 : ℝ × ℝ → ℝ² := fun p => !₂[p.1, p.2]
  have hmp : MeasurePreserving toLp2 volume volume := by
    have heq : toLp2 = (WithLp.toLp 2 : (Fin 2 → ℝ) → ℝ²) ∘ MeasurableEquiv.finTwoArrow.symm := by
      funext ⟨a, b⟩
      ext i; fin_cases i <;> simp [toLp2, MeasurableEquiv.finTwoArrow]
    rw [heq]
    exact (PiLp.volume_preserving_toLp (Fin 2)).comp
      (MeasureTheory.volume_preserving_finTwoArrow ℝ).symm
  rw [← hmp.measure_preimage cap0_measurable.nullMeasurableSet]
  let box : Set (ℝ × ℝ) :=
    {p : ℝ × ℝ | p.2 ∈ Set.Icc (-y₀) y₀ ∧ p.1 ∈ Set.Icc hC (1 / 2 - p.2 ^ 2 - p.2 ^ 4)}
  have hsub : toLp2 ⁻¹' cap0 ⊆ box := by
    rintro ⟨x, y⟩ ⟨hnorm, hxh⟩
    simp only [toLp2, Matrix.cons_val_zero] at hxh
    have hsq : x ^ 2 + y ^ 2 < 1 / 4 := by
      have h1 : ‖toLp2 (x, y)‖ ^ 2 < (1 / 2) ^ 2 := by
        nlinarith [norm_nonneg (toLp2 (x, y))]
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] at h1
      simp only [toLp2, Matrix.cons_val_zero, Matrix.cons_val_one] at h1
      linarith
    have hy_sq : y ^ 2 < y₀ ^ 2 := by nlinarith [hC_y₀_sq, hC_pos]
    have hy_abs : |y| ≤ y₀ := by
      have := sq_le_sq.mp hy_sq.le
      rwa [abs_of_pos y₀_pos] at this
    have hy_mem : y ∈ Set.Icc (-y₀) y₀ := abs_le.mp hy_abs
    have hpoly_nonneg : 0 ≤ 1 / 2 - y ^ 2 - y ^ 4 := by
      have hy1 : y ^ 2 ≤ (1 / 4 : ℝ) := by
        have hy02 : y₀ ^ 2 ≤ (1 / 4 : ℝ) := by unfold y₀; norm_num
        linarith
      nlinarith
    have hpoly_sq : 1 / 4 - y ^ 2 ≤ (1 / 2 - y ^ 2 - y ^ 4) ^ 2 := by
      have hdiff : (1 / 2 - y ^ 2 - y ^ 4) ^ 2 - (1 / 4 - y ^ 2) = 2 * y ^ 6 + y ^ 8 := by ring
      have hpos : 0 ≤ 2 * y ^ 6 + y ^ 8 := by positivity
      linarith
    have hx_le : x ≤ 1 / 2 - y ^ 2 - y ^ 4 := by
      have hx_sq : x ^ 2 ≤ (1 / 2 - y ^ 2 - y ^ 4) ^ 2 := by linarith
      nlinarith [hC_pos]
    exact ⟨hy_mem, hxh, hx_le⟩
  have hbox_meas : MeasurableSet box := by
    have h1 : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Set.Icc (-y₀) y₀} :=
      measurableSet_Icc.preimage measurable_snd
    have h2 : MeasurableSet {p : ℝ × ℝ | hC ≤ p.1} :=
      measurableSet_le measurable_const measurable_fst
    have h3 : MeasurableSet {p : ℝ × ℝ | p.1 ≤ 1 / 2 - p.2 ^ 2 - p.2 ^ 4} :=
      measurableSet_le measurable_fst (by fun_prop)
    exact h1.inter (h2.inter h3)
  have hbox_vol : volume box = ENNReal.ofReal capUB := by
    rw [Measure.volume_eq_prod, Measure.prod_apply_symm hbox_meas]
    have hslice : ∀ y : ℝ, volume ((fun x : ℝ => (x, y)) ⁻¹' box) =
        (Set.Icc (-y₀) y₀).indicator (fun y => ENNReal.ofReal ((1 / 2 - y ^ 2 - y ^ 4) - hC)) y := by
      intro y
      by_cases hy : y ∈ Set.Icc (-y₀) y₀
      · simp only [Set.indicator_of_mem hy]
        have hpre : (fun x : ℝ => (x, y)) ⁻¹' box = Set.Icc hC (1 / 2 - y ^ 2 - y ^ 4) := by
          ext x; simp only [Set.mem_preimage, box, Set.mem_ofPred_eq, hy, true_and]
        rw [hpre, Real.volume_Icc]
      · simp only [Set.indicator_of_notMem hy]
        have hpre : (fun x : ℝ => (x, y)) ⁻¹' box = ∅ := by
          ext x; simp only [Set.mem_preimage, box, Set.mem_ofPred_eq, hy, false_and,
            Set.mem_empty_iff_false]
        rw [hpre, measure_empty]
    simp_rw [hslice]
    rw [lintegral_indicator measurableSet_Icc]
    have hfn_nonneg : ∀ y ∈ Set.Icc (-y₀) y₀, 0 ≤ (1 / 2 - y ^ 2 - y ^ 4) - hC := by
      intro y hy
      have hy_sq : y ^ 2 ≤ y₀ ^ 2 := by nlinarith [hy.1, hy.2]
      have h1 : y ^ 4 ≤ y₀ ^ 4 := by nlinarith [sq_nonneg y, sq_nonneg y₀]
      have h2 : y₀ ^ 2 + y₀ ^ 4 ≤ 1 / 2 - hC := by unfold y₀ hC; norm_num
      linarith
    have hcont : ContinuousOn (fun y : ℝ => (1 / 2 - y ^ 2 - y ^ 4) - hC) (Set.Icc (-y₀) y₀) := by
      fun_prop
    have hint : IntegrableOn (fun y : ℝ => (1 / 2 - y ^ 2 - y ^ 4) - hC) (Set.Icc (-y₀) y₀) :=
      hcont.integrableOn_Icc
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_restrict_of_forall_mem measurableSet_Icc hfn_nonneg)]
    congr 1
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [y₀_pos] : -y₀ ≤ y₀)]
    have hrew : (fun y : ℝ => (1 / 2 - y ^ 2 - y ^ 4) - hC) =
        (fun y : ℝ => (1 / 2 - hC) - y ^ 2 - y ^ 4) := by funext y; ring
    rw [hrew]
    have hi1 : IntervalIntegrable (fun _ : ℝ => 1 / 2 - hC) volume (-y₀) y₀ :=
      intervalIntegrable_const
    have hi2 : IntervalIntegrable (fun y : ℝ => y ^ 2) volume (-y₀) y₀ :=
      (continuous_pow 2).intervalIntegrable _ _
    have hi3 : IntervalIntegrable (fun y : ℝ => y ^ 4) volume (-y₀) y₀ :=
      (continuous_pow 4).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub (hi1.sub hi2) hi3,
      intervalIntegral.integral_sub hi1 hi2,
      intervalIntegral.integral_const, integral_pow, integral_pow]
    simp only [smul_eq_mul]
    unfold capUB
    ring
  exact (measure_mono hsub).trans_eq hbox_vol

private lemma volume_ball_R2 (x : ℝ²) (r : ℝ) (hr : 0 ≤ r) :
    volume (Metric.ball x r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin]
  have hpi : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  rw [show ((2 : ℕ) : ℝ) / 2 + 1 = 2 by norm_num, Real.Gamma_two, div_one, hpi]
  rw [← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (pow_nonneg hr 2), mul_comm]

private lemma tortoise_volume_ge : ENNReal.ofReal croftAreaLB ≤ volume tortoise := by
  have h3 := sqrt3_sq
  let R₀ := mkOrtho 1 0 0 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  let R₁ := mkOrtho (-1) 0 0 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  let R₂ := mkOrtho (1 / 2) (Real.sqrt 3 / 2) (-(Real.sqrt 3 / 2)) (1 / 2)
    (by nlinarith) (by nlinarith) (by ring) (by nlinarith) (by nlinarith) (by ring)
  let R₃ := mkOrtho (-(1 / 2)) (-(Real.sqrt 3 / 2)) (-(Real.sqrt 3 / 2)) (1 / 2)
    (by nlinarith) (by nlinarith) (by ring) (by nlinarith) (by nlinarith) (by ring)
  let R₄ := mkOrtho (-(1 / 2)) (Real.sqrt 3 / 2) (-(Real.sqrt 3 / 2)) (-(1 / 2))
    (by nlinarith) (by nlinarith) (by ring) (by nlinarith) (by nlinarith) (by ring)
  let R₅ := mkOrtho (1 / 2) (-(Real.sqrt 3 / 2)) (-(Real.sqrt 3 / 2)) (-(1 / 2))
    (by nlinarith) (by nlinarith) (by ring) (by nlinarith) (by nlinarith) (by ring)
  have hcover : Metric.ball (0 : ℝ²) (1 / 2) ⊆
      tortoise ∪ (R₀ ⁻¹' cap0 ∪ (R₁ ⁻¹' cap0 ∪ (R₂ ⁻¹' cap0 ∪
        (R₃ ⁻¹' cap0 ∪ (R₄ ⁻¹' cap0 ∪ R₅ ⁻¹' cap0))))) := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    by_cases h1 : |x 0| < hC
    · by_cases h2 : |x 0 / 2 + Real.sqrt 3 / 2 * x 1| < hC
      · by_cases h3' : |-(x 0 / 2) + Real.sqrt 3 / 2 * x 1| < hC
        · exact Or.inl ⟨hx, h1, h2, h3'⟩
        · push Not at h3'
          rcases le_or_gt 0 (-(x 0 / 2) + Real.sqrt 3 / 2 * x 1) with hp | hn
          · right; right; right; right; right; left
            refine ⟨by rw [R₄.norm_map]; exact hx, ?_⟩
            simp only [R₄, mkOrtho, LinearIsometryEquiv.coe_mk, LinearEquiv.coe_mk,
              LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero]
            rw [abs_of_nonneg hp] at h3'; linarith
          · right; right; right; right; right; right
            refine ⟨by rw [R₅.norm_map]; exact hx, ?_⟩
            simp only [R₅, mkOrtho, LinearIsometryEquiv.coe_mk, LinearEquiv.coe_mk,
              LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero]
            rw [abs_of_neg hn] at h3'; linarith
      · push Not at h2
        rcases le_or_gt 0 (x 0 / 2 + Real.sqrt 3 / 2 * x 1) with hp | hn
        · right; right; right; left
          refine ⟨by rw [R₂.norm_map]; exact hx, ?_⟩
          simp only [R₂, mkOrtho, LinearIsometryEquiv.coe_mk, LinearEquiv.coe_mk,
            LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero]
          rw [abs_of_nonneg hp] at h2; linarith
        · right; right; right; right; left
          refine ⟨by rw [R₃.norm_map]; exact hx, ?_⟩
          simp only [R₃, mkOrtho, LinearIsometryEquiv.coe_mk, LinearEquiv.coe_mk,
            LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero]
          rw [abs_of_neg hn] at h2; linarith
    · push Not at h1
      rcases le_or_gt 0 (x 0) with hp | hn
      · right; left
        refine ⟨by rw [R₀.norm_map]; exact hx, ?_⟩
        simp only [R₀, mkOrtho, LinearIsometryEquiv.coe_mk, LinearEquiv.coe_mk,
          LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero]
        rw [abs_of_nonneg hp] at h1; linarith
      · right; right; left
        refine ⟨by rw [R₁.norm_map]; exact hx, ?_⟩
        simp only [R₁, mkOrtho, LinearIsometryEquiv.coe_mk, LinearEquiv.coe_mk,
          LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero]
        rw [abs_of_neg hn] at h1; linarith
  have hvol_ball : volume (Metric.ball (0 : ℝ²) (1 / 2)) = ENNReal.ofReal (Real.pi / 4) := by
    rw [volume_ball_R2 0 (1 / 2) (by norm_num)]
    congr 1; ring
  have hvol_cap : ∀ R : ℝ² ≃ₗᵢ[ℝ] ℝ², volume (R ⁻¹' cap0) ≤ ENNReal.ofReal capUB := fun R => by
    rw [R.measurePreserving.measure_preimage cap0_measurable.nullMeasurableSet]
    exact cap0_volume_le
  have hsubadd : ENNReal.ofReal (Real.pi / 4) ≤ volume tortoise + 6 * ENNReal.ofReal capUB := by
    calc ENNReal.ofReal (Real.pi / 4)
        = volume (Metric.ball (0 : ℝ²) (1 / 2)) := hvol_ball.symm
      _ ≤ volume (tortoise ∪ (R₀ ⁻¹' cap0 ∪ (R₁ ⁻¹' cap0 ∪ (R₂ ⁻¹' cap0 ∪
            (R₃ ⁻¹' cap0 ∪ (R₄ ⁻¹' cap0 ∪ R₅ ⁻¹' cap0)))))) := measure_mono hcover
      _ ≤ volume tortoise + (volume (R₀ ⁻¹' cap0) + (volume (R₁ ⁻¹' cap0) +
            (volume (R₂ ⁻¹' cap0) + (volume (R₃ ⁻¹' cap0) +
              (volume (R₄ ⁻¹' cap0) + volume (R₅ ⁻¹' cap0)))))) := by
          refine (measure_union_le _ _).trans ?_
          gcongr
          refine (measure_union_le _ _).trans ?_
          gcongr
          refine (measure_union_le _ _).trans ?_
          gcongr
          refine (measure_union_le _ _).trans ?_
          gcongr
          refine (measure_union_le _ _).trans ?_
          gcongr
          exact measure_union_le _ _
      _ ≤ volume tortoise + (ENNReal.ofReal capUB + (ENNReal.ofReal capUB +
            (ENNReal.ofReal capUB + (ENNReal.ofReal capUB +
              (ENNReal.ofReal capUB + ENNReal.ofReal capUB))))) := by
          gcongr <;> exact hvol_cap _
      _ = volume tortoise + 6 * ENNReal.ofReal capUB := by ring
  have hcap_nonneg : 0 ≤ capUB := by unfold capUB y₀ hC; norm_num
  have hsum : ENNReal.ofReal croftAreaLB + 6 * ENNReal.ofReal capUB =
      ENNReal.ofReal (Real.pi / 4) := by
    have h6 : (6 : ENNReal) * ENNReal.ofReal capUB = ENNReal.ofReal (6 * capUB) := by
      rw [← ENNReal.ofReal_ofNat 6, ← ENNReal.ofReal_mul (by norm_num)]
    rw [h6, ← ENNReal.ofReal_add croftAreaLB_pos.le (by positivity)]
    congr 1; unfold croftAreaLB; ring
  have hfin : (6 : ENNReal) * ENNReal.ofReal capUB ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  rw [← hsum] at hsubadd
  exact (ENNReal.add_le_add_iff_right hfin).mp hsubadd

/- ## Density bound for `croftSet` -/

private lemma ballDensity_nonneg (A : Set ℝ²) (R : ℝ) : 0 ≤ Erdos232.ballDensity A R := by
  unfold Erdos232.ballDensity; positivity

private lemma ballDensity_le_one (A : Set ℝ²) (R : ℝ) : Erdos232.ballDensity A R ≤ 1 := by
  unfold Erdos232.ballDensity
  by_cases hR : R ≤ 0
  · have hb : Metric.ball (0 : ℝ²) R = ∅ := Metric.ball_eq_empty.mpr hR
    simp [hb]
  · push Not at hR
    have hvol := volume_ball_R2 0 R hR.le
    have hne_top : volume (Metric.ball (0 : ℝ²) R) ≠ ⊤ := by rw [hvol]; exact ENNReal.ofReal_ne_top
    have hpos : 0 < (volume (Metric.ball (0 : ℝ²) R)).toReal := by
      rw [hvol, ENNReal.toReal_ofReal (by positivity)]; positivity
    rw [div_le_one hpos]
    exact ENNReal.toReal_mono hne_top (measure_mono Set.inter_subset_right)

private lemma upperDensity_le_one (A : Set ℝ²) : Erdos232.upperDensity A ≤ 1 := by
  unfold Erdos232.upperDensity
  apply Filter.limsup_le_of_le
  · exact Filter.isCoboundedUnder_le_of_le Filter.atTop (fun R => ballDensity_nonneg A R)
  · exact Filter.Eventually.of_forall (fun R => ballDensity_le_one A R)

private lemma ballDensity_croftSet_ge (R : ℝ) (hR : 4 < R) :
    croftDensLB * ((R - 4) / R) ^ 2 ≤ Erdos232.ballDensity croftSet R := by
  let S : Finset (ℤ × ℤ) := (latP_finite (R - 1)).toFinset
  have hsub : (⋃ p ∈ S, tortoiseAt p) ⊆ croftSet ∩ Metric.ball 0 R := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨p, hpS, hxp⟩
    refine ⟨Set.mem_iUnion.mpr ⟨p, hxp⟩, ?_⟩
    have hp : ‖latP p‖ ≤ R - 1 := by simpa [S] using hpS
    have hxb := Metric.mem_ball.mp (tortoiseAt_subset_ball p hxp)
    rw [Metric.mem_ball, dist_zero_right]
    rw [dist_eq_norm] at hxb
    have htri : ‖x‖ ≤ ‖x - latP p‖ + ‖latP p‖ := by
      simpa [sub_add_cancel] using norm_add_le (x - latP p) (latP p)
    linarith
  have hdisj : Set.PairwiseDisjoint (↑S : Set (ℤ × ℤ)) tortoiseAt :=
    fun p _ q _ hpq => tortoiseAt_disjoint p q hpq
  have hvol_low_enn :
      (S.card : ENNReal) * ENNReal.ofReal croftAreaLB ≤ volume (croftSet ∩ Metric.ball 0 R) := by
    calc (S.card : ENNReal) * ENNReal.ofReal croftAreaLB
        = ∑ _p ∈ S, ENNReal.ofReal croftAreaLB := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ S, volume (tortoiseAt p) := by
          gcongr with p _
          rw [tortoiseAt_volume]
          exact tortoise_volume_ge
      _ = volume (⋃ p ∈ S, tortoiseAt p) :=
          (measure_biUnion_finset hdisj (fun p _ => (tortoiseAt_isOpen p).measurableSet)).symm
      _ ≤ volume (croftSet ∩ Metric.ball 0 R) := measure_mono hsub
  have hcov : Metric.ball (0 : ℝ²) (R - 4) ⊆ ⋃ p ∈ S, latCell p := by
    intro x hx
    obtain ⟨p, hxp⟩ := latCell_cover x
    refine Set.mem_iUnion₂.mpr ⟨p, ?_, hxp⟩
    change p ∈ (latP_finite (R - 1)).toFinset
    rw [Set.Finite.mem_toFinset]
    change ‖latP p‖ ≤ R - 1
    rw [Metric.mem_ball, dist_zero_right] at hx
    have hdiff := norm_sub_latP_lt_three p hxp
    have htri : ‖latP p‖ ≤ ‖x‖ + ‖x - latP p‖ := by
      simpa [sub_sub_cancel] using norm_sub_le x (x - latP p)
    linarith
  have hvol_cov_enn :
      ENNReal.ofReal (Real.pi * (R - 4) ^ 2) ≤ (S.card : ENNReal) * ENNReal.ofReal cellArea := by
    calc ENNReal.ofReal (Real.pi * (R - 4) ^ 2)
        = volume (Metric.ball (0 : ℝ²) (R - 4)) := (volume_ball_R2 0 (R - 4) (by linarith)).symm
      _ ≤ volume (⋃ p ∈ S, latCell p) := measure_mono hcov
      _ ≤ ∑ p ∈ S, volume (latCell p) := measure_biUnion_finset_le S latCell
      _ = (S.card : ENNReal) * ENNReal.ofReal cellArea := by
          simp [latCell_volume, Finset.sum_const, nsmul_eq_mul]
  have hballR_vol : volume (Metric.ball (0 : ℝ²) R) = ENNReal.ofReal (Real.pi * R ^ 2) :=
    volume_ball_R2 0 R (by linarith)
  have hne_top_inter : volume (croftSet ∩ Metric.ball (0 : ℝ²) R) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_right)
    rw [hballR_vol]; exact ENNReal.ofReal_ne_top
  have hlow_real : (S.card : ℝ) * croftAreaLB ≤ (volume (croftSet ∩ Metric.ball 0 R)).toReal := by
    have h := ENNReal.toReal_mono hne_top_inter hvol_low_enn
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal croftAreaLB_pos.le] at h
  have hcov_real : Real.pi * (R - 4) ^ 2 ≤ (S.card : ℝ) * cellArea := by
    have hne : (S.card : ENNReal) * ENNReal.ofReal cellArea ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
    have h := ENNReal.toReal_mono hne hvol_cov_enn
    rwa [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal cellArea_pos.le] at h
  have hS_ge : Real.pi * (R - 4) ^ 2 / cellArea ≤ (S.card : ℝ) := by
    rw [div_le_iff₀ cellArea_pos]; exact hcov_real
  have hnum_ge : Real.pi * (R - 4) ^ 2 / cellArea * croftAreaLB ≤
      (volume (croftSet ∩ Metric.ball 0 R)).toReal :=
    le_trans (mul_le_mul_of_nonneg_right hS_ge croftAreaLB_pos.le) hlow_real
  unfold Erdos232.ballDensity
  rw [hballR_vol, ENNReal.toReal_ofReal (by positivity), le_div_iff₀ (by positivity)]
  have hR_pos : 0 < R := by linarith
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hca_pos : 0 < cellArea := cellArea_pos
  have halg : croftDensLB * ((R - 4) / R) ^ 2 * (Real.pi * R ^ 2) =
      Real.pi * (R - 4) ^ 2 / cellArea * croftAreaLB := by
    unfold croftDensLB
    field_simp
  linarith

private lemma croftSet_upperDensity_ge : croftDensLB ≤ Erdos232.upperDensity croftSet := by
  let g : ℝ → ℝ := fun R => croftDensLB * ((R - 4) / R) ^ 2
  have hg_tendsto : Filter.Tendsto g Filter.atTop (nhds croftDensLB) := by
    have hinv : Filter.Tendsto (fun R : ℝ => (4 : ℝ) / R) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop Filter.tendsto_id
    have h1 : Filter.Tendsto (fun R : ℝ => 1 - (4 : ℝ) / R) Filter.atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hinv
    have h2 : Filter.Tendsto (fun R : ℝ => (R - 4) / R) Filter.atTop (nhds 1) := by
      refine h1.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
      field_simp
    have h3 : Filter.Tendsto (fun R : ℝ => ((R - 4) / R) ^ 2) Filter.atTop (nhds 1) := by
      simpa using h2.pow 2
    simpa using (tendsto_const_nhds.mul h3)
  have hle : g ≤ᶠ[Filter.atTop] Erdos232.ballDensity croftSet := by
    filter_upwards [Filter.eventually_gt_atTop (4 : ℝ)] with R hR
    exact ballDensity_croftSet_ge R hR
  have hlim_le : Filter.limsup g Filter.atTop ≤ Erdos232.upperDensity croftSet := by
    unfold Erdos232.upperDensity
    refine Filter.limsup_le_limsup hle ?_ ?_
    · exact hg_tendsto.isBoundedUnder_ge.isCoboundedUnder_le
    · exact Filter.isBoundedUnder_of ⟨1, fun R => ballDensity_le_one croftSet R⟩
  rwa [hg_tendsto.limsup_eq] at hlim_le

end OMA_Erdos232_Croft

theorem OMA.solution : type_of% @Erdos232.erdos_232.variants.croft_lower_bound := by
  refine le_trans OMA_Erdos232_Croft.croftDensLB_ge
    (le_trans OMA_Erdos232_Croft.croftSet_upperDensity_ge ?_)
  unfold Erdos232.m₁
  refine le_csSup ?_ ⟨OMA_Erdos232_Croft.croftSet, OMA_Erdos232_Croft.croftSet_nullMeasurable,
    OMA_Erdos232_Croft.croftSet_unitDistanceAvoiding, rfl⟩
  refine ⟨1, ?_⟩
  rintro d ⟨A, _, _, rfl⟩
  exact OMA_Erdos232_Croft.upperDensity_le_one A
