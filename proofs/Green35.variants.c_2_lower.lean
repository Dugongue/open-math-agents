import FormalConjectures.GreensOpenProblems.«35»
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Proof of Ben Green's Open Problem 35 (`c 2 ≥ √(4/7)`)

We prove `ENNReal.ofReal (Real.sqrt (4 / 7)) ≤ Green35.c 2` using the continuous Fourier-analytic
form of Green's argument ([Gr01], §5) on the circle `AddCircle (2 : ℝ)`, with the degree-6 test
polynomial `p₆(t) = (7 / 3) * (1 - (2 * t) ^ 6)` on `[-1/2, 1/2]`.

Let `U : C(AddCircle 2, ℂ)` equal `1` on `[0, 1]` and `1 - p₆(x - 3/2)` on `[1, 2]`. Since `U` is
continuous with `U 0 = U 2 = 1` and its Fourier coefficients decay as `O(1 / n²)`, its Fourier
series converges pointwise everywhere to `U` with `fourierCoeff U 0 = 0` and
`‖fourierCoeff U n‖ = pHat |n| / 2` for `n ≠ 0`.

For any unit-interval density `f`, pairing `f` with `U` gives
`1 = ∫ f · U = ∑' n, fourierCoeff U n * c n`, whence
`1 ≤ ∑' r, pHat (r + 1) * ‖c (r + 1)‖`, where `c n = ∫ x, f(x) * exp(i π n x)`.
Applying Hölder's inequality with exponents `(4/3, 4)` and Bessel's inequality on `[0, 2]` to
`f ⋆ f` (whose `n`-th Fourier coefficient is `c n ^ 2`) yields
`1 ≤ (∑' r, pHat (r + 1) ^ (4/3)) ^ 3 * (∫ (f ⋆ f)² - 1/2)`.
Using closed-form integration by parts for `pHat r`, an explicit 20-term rational bound plus
telescoping tail bounds show `(∑' r, pHat (r + 1) ^ (4/3)) ^ 3 ≤ (24093 / 10000) ^ 3 ≤ 14`,
giving `∫ (f ⋆ f)² ≥ 1/2 + 1/14 = 4/7`.
-/

namespace OMA_Green35_c2

open MeasureTheory Filter Topology
open scoped Convolution ENNReal Real

private instance : Fact ((0 : ℝ) < 2) := ⟨by norm_num⟩

/- ## Elementary helpers for `fourier` on `AddCircle (2 : ℝ)` -/

private lemma fourier2_coe (n : ℤ) (x : ℝ) :
    @fourier 2 n (x : AddCircle (2 : ℝ)) = Complex.exp (Real.pi * Complex.I * n * x) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast; ring

private lemma fourier2_norm (n : ℤ) (x : ℝ) :
    ‖@fourier 2 n (x : AddCircle (2 : ℝ))‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

private lemma fourier2_zero (x : ℝ) :
    @fourier 2 0 (x : AddCircle (2 : ℝ)) = 1 := by
  simp

private lemma fourier2_add (n : ℤ) (x y : ℝ) :
    @fourier 2 n ((x + y : ℝ) : AddCircle (2 : ℝ)) =
      @fourier 2 n (x : AddCircle (2 : ℝ)) * @fourier 2 n (y : AddCircle (2 : ℝ)) := by
  rw [fourier2_coe, fourier2_coe, fourier2_coe, ← Complex.exp_add]
  congr 1; push_cast; ring

private lemma fourier2_mul_conj (n m : ℤ) (x : ℝ) :
    @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * starRingEnd ℂ (@fourier 2 (-m) (x : AddCircle (2 : ℝ))) =
      @fourier 2 (m - n) (x : AddCircle (2 : ℝ)) := by
  rw [← fourier_neg, neg_neg, fourier2_coe, fourier2_coe, fourier2_coe, ← Complex.exp_add]
  congr 1; push_cast; ring

private lemma intervalIntegral_fourier2 (k : ℤ) :
    ∫ x in (0 : ℝ)..2, @fourier 2 k (x : AddCircle (2 : ℝ)) = if k = 0 then (2 : ℂ) else 0 := by
  split_ifs with hk
  · subst hk
    simp_rw [fourier2_zero]
    simp
  · simp_rw [fourier2_coe]
    let c : ℂ := Real.pi * Complex.I * (k : ℂ)
    have hc : c ≠ 0 := by
      simp only [c, ne_eq, mul_eq_zero, Complex.ofReal_eq_zero, Real.pi_ne_zero,
        Complex.I_ne_zero, Int.cast_eq_zero, hk, or_self, not_false_eq_true]
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 2,
        HasDerivAt (fun t : ℝ => Complex.exp (c * t) / c) (Complex.exp (c * x)) x := by
      intro x _
      have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) (c * 1) x :=
        (Complex.ofRealCLM.hasDerivAt).const_mul c
      rw [mul_one] at h1
      have h2 : HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ)))
          (Complex.exp (c * (x : ℂ)) * c) x := h1.cexp
      have h3 := h2.div_const c
      rwa [mul_div_cancel_right₀ _ hc] at h3
    have hint : IntervalIntegrable (fun x : ℝ => Complex.exp (c * (x : ℂ))) volume 0 2 :=
      (Continuous.intervalIntegrable (by fun_prop) 0 2)
    have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hrew : (fun x : ℝ => Complex.exp (Real.pi * Complex.I * (k : ℂ) * (x : ℂ))) =
        (fun x : ℝ => Complex.exp (c * (x : ℂ))) := rfl
    rw [hrew, hval]
    have hexp2 : Complex.exp (c * (2 : ℂ)) = 1 := by
      have : c * (2 : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by simp only [c]; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    simp [hexp2]

/- ## The degree-6 test polynomial and continuous circle function `U` -/

private noncomputable def p6 (t : ℝ) : ℝ :=
  (7 / 3 : ℝ) * (1 - (2 * t) ^ 6)

private lemma p6_even (t : ℝ) : p6 (-t) = p6 t := by
  unfold p6; ring

private lemma p6_end_neg : p6 (-1 / 2) = 0 := by
  unfold p6; norm_num

private lemma p6_end_pos : p6 (1 / 2) = 0 := by
  unfold p6; norm_num

private lemma integral_p6 : ∫ t in (-1 / 2 : ℝ)..(1 / 2), p6 t = 2 := by
  have hrew : (fun t : ℝ => p6 t) = fun t : ℝ => (7 / 3 : ℝ) - (448 / 3 : ℝ) * t ^ 6 := by
    funext t; unfold p6; ring
  rw [hrew, intervalIntegral.integral_sub intervalIntegrable_const
    ((continuous_pow 6).intervalIntegrable _ _ |>.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    integral_pow]
  norm_num

private noncomputable def uRaw (x : ℝ) : ℂ :=
  if x ≤ 1 then (1 : ℂ) else ((1 - p6 (x - 3 / 2) : ℝ) : ℂ)

private lemma uRaw_zero : uRaw 0 = 1 := by
  simp [uRaw]

private lemma uRaw_two : uRaw 2 = 1 := by
  have h2 : ¬ ((2 : ℝ) ≤ 1) := by norm_num
  have hsub : (2 : ℝ) - 3 / 2 = 1 / 2 := by norm_num
  simp only [uRaw, h2, ↓reduceIte, hsub, p6_end_pos, sub_zero, Complex.ofReal_one]

private lemma uRaw_continuous : Continuous uRaw := by
  have hc1 : Continuous (fun _ : ℝ => (1 : ℂ)) := continuous_const
  have hc2 : Continuous (fun x : ℝ => ((1 - p6 (x - 3 / 2) : ℝ) : ℂ)) := by
    unfold p6; fun_prop
  refine Continuous.if_le hc1 hc2 continuous_id continuous_const ?_
  intro x hx
  have hx1 : x = 1 := hx
  subst hx1
  have hsub : (1 : ℝ) - 3 / 2 = -1 / 2 := by norm_num
  simp [hsub, p6_end_neg]

private noncomputable def U : C(AddCircle (2 : ℝ), ℂ) :=
  ⟨AddCircle.liftIco (2 : ℝ) 0 uRaw,
    AddCircle.liftIco_zero_continuous (by rw [uRaw_zero, uRaw_two]) uRaw_continuous.continuousOn⟩

private lemma U_coe_of_mem_Ico {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 2) :
    U (x : AddCircle (2 : ℝ)) = uRaw x := by
  change AddCircle.liftIco (2 : ℝ) 0 uRaw x = uRaw x
  exact AddCircle.liftIco_zero_coe_apply hx

private lemma U_coe_of_mem_Icc01 {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    U (x : AddCircle (2 : ℝ)) = 1 := by
  rw [U_coe_of_mem_Ico ⟨hx.1, by linarith [hx.2]⟩]
  simp [uRaw, hx.2]

private lemma U_coe_two : U ((2 : ℝ) : AddCircle (2 : ℝ)) = 1 := by
  have h0 : ((2 : ℝ) : AddCircle (2 : ℝ)) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨1, by norm_num⟩
  rw [h0, ← QuotientAddGroup.mk_zero, U_coe_of_mem_Ico ⟨le_rfl, by norm_num⟩, uRaw_zero]

private lemma U_coe_eq_uRaw_on_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    U (x : AddCircle (2 : ℝ)) = uRaw x := by
  by_cases hlt : x < 2
  · exact U_coe_of_mem_Ico ⟨hx.1, hlt⟩
  · have hx2 : x = 2 := le_antisymm hx.2 (le_of_not_gt hlt)
    subst hx2
    rw [U_coe_two, uRaw_two]

/- ## Fourier coefficients of `U` and exact closed-form integration by parts -/

private noncomputable def pHat (r : ℕ) : ℝ :=
  |∫ t in (-1 / 2 : ℝ)..(1 / 2), p6 t * Real.cos (Real.pi * (r : ℝ) * t)|

private lemma integral_p6_mul_exp (n : ℤ) :
    ∫ t in (-1 / 2 : ℝ)..(1 / 2),
        (p6 t : ℂ) * Complex.exp (-(Real.pi * Complex.I * (n : ℂ) * (t : ℂ))) =
      ((∫ t in (-1 / 2 : ℝ)..(1 / 2), p6 t * Real.cos (Real.pi * (n : ℝ) * t) : ℝ) : ℂ) := by
  have hsplit : ∀ t : ℝ,
      (p6 t : ℂ) * Complex.exp (-(Real.pi * Complex.I * (n : ℂ) * (t : ℂ))) =
        ((p6 t * Real.cos (Real.pi * (n : ℝ) * t) : ℝ) : ℂ) -
        Complex.I * ((p6 t * Real.sin (Real.pi * (n : ℝ) * t) : ℝ) : ℂ) := by
    intro t
    have harg : -(Real.pi * Complex.I * (n : ℂ) * (t : ℂ)) =
        ((-(Real.pi * (n : ℝ) * t) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [harg, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  simp_rw [hsplit]
  have hi_cos : IntervalIntegrable
      (fun t : ℝ => ((p6 t * Real.cos (Real.pi * (n : ℝ) * t) : ℝ) : ℂ)) volume (-1 / 2) (1 / 2) :=
    (Continuous.intervalIntegrable (by unfold p6; fun_prop) _ _)
  have hi_sin : IntervalIntegrable
      (fun t : ℝ => Complex.I * ((p6 t * Real.sin (Real.pi * (n : ℝ) * t) : ℝ) : ℂ))
      volume (-1 / 2) (1 / 2) :=
    (Continuous.intervalIntegrable (by unfold p6; fun_prop) _ _)
  rw [intervalIntegral.integral_sub hi_cos hi_sin, intervalIntegral.integral_const_mul]
  have hsin_zero : ∫ t in (-1 / 2 : ℝ)..(1 / 2), p6 t * Real.sin (Real.pi * (n : ℝ) * t) = 0 := by
    have hneg : ∫ t in (-1 / 2 : ℝ)..(1 / 2), p6 t * Real.sin (Real.pi * (n : ℝ) * t) =
        ∫ t in (-1 / 2 : ℝ)..(1 / 2), p6 (-t) * Real.sin (Real.pi * (n : ℝ) * (-t)) := by
      have h := intervalIntegral.integral_comp_neg
        (f := fun t : ℝ => p6 t * Real.sin (Real.pi * (n : ℝ) * t)) (a := (-1 / 2 : ℝ)) (b := 1 / 2)
      rw [show -(-1 / 2 : ℝ) = 1 / 2 by norm_num, show -(1 / 2 : ℝ) = -1 / 2 by norm_num] at h
      exact h.symm
    have hodd : (fun t : ℝ => p6 (-t) * Real.sin (Real.pi * (n : ℝ) * (-t))) =
        fun t : ℝ => -(p6 t * Real.sin (Real.pi * (n : ℝ) * t)) := by
      funext t; rw [p6_even, mul_neg, Real.sin_neg]; ring
    rw [hodd, intervalIntegral.integral_neg] at hneg
    linarith
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal, hsin_zero]
  simp

private lemma fourierCoeff_U_zero : fourierCoeff U 0 = 0 := by
  rw [fourierCoeff_eq_intervalIntegral U 0 0]
  have h02 : (0 : ℝ) + 2 = 2 := by norm_num
  rw [h02]
  have heq : Set.EqOn (fun x : ℝ => @fourier 2 (-0) (x : AddCircle (2 : ℝ)) • U x)
      uRaw (Set.uIcc 0 2) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hx
    simp only [neg_zero, fourier2_zero, smul_eq_mul, one_mul, U_coe_eq_uRaw_on_Icc hx]
  rw [intervalIntegral.integral_congr heq]
  have hi1 : IntervalIntegrable uRaw volume 0 1 := uRaw_continuous.intervalIntegrable 0 1
  have hi2 : IntervalIntegrable uRaw volume 1 2 := uRaw_continuous.intervalIntegrable 1 2
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have hpart1 : ∫ x in (0 : ℝ)..1, uRaw x = 1 := by
    have h1 : Set.EqOn uRaw (fun _ => (1 : ℂ)) (Set.uIcc 0 1) := by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      simp [uRaw, hx.2]
    rw [intervalIntegral.integral_congr h1]
    simp
  have hpart2 : ∫ x in (1 : ℝ)..2, uRaw x = -1 := by
    have h2 : Set.EqOn uRaw (fun x : ℝ => ((1 - p6 (x - 3 / 2) : ℝ) : ℂ)) (Set.uIcc 1 2) := by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
      by_cases hx1 : x ≤ 1
      · have : x = 1 := le_antisymm hx1 hx.1
        subst this
        have hsub : (1 : ℝ) - 3 / 2 = -1 / 2 := by norm_num
        simp [uRaw, hsub, p6_end_neg]
      · simp [uRaw, hx1]
    rw [intervalIntegral.integral_congr h2, intervalIntegral.integral_ofReal]
    have hr : ∫ x in (1 : ℝ)..2, (1 - p6 (x - 3 / 2)) = -1 := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        (Continuous.intervalIntegrable (by unfold p6; fun_prop) 1 2)]
      have hshift := intervalIntegral.integral_comp_sub_right p6 (3 / 2 : ℝ) (a := (1 : ℝ)) (b := 2)
      rw [show (1 : ℝ) - 3 / 2 = -1 / 2 by norm_num, show (2 : ℝ) - 3 / 2 = 1 / 2 by norm_num] at hshift
      rw [hshift, integral_p6]
      norm_num
    rw [hr]; norm_num
  rw [hpart1, hpart2]; simp

private lemma norm_fourierCoeff_U (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeff U n‖ = pHat n.natAbs / 2 := by
  rw [fourierCoeff_eq_intervalIntegral U n 0]
  have h02 : (0 : ℝ) + 2 = 2 := by norm_num
  rw [h02]
  have heq : Set.EqOn (fun x : ℝ => @fourier 2 (-n) (x : AddCircle (2 : ℝ)) • U x)
      (fun x : ℝ => @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * uRaw x) (Set.uIcc 0 2) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hx
    simp only [smul_eq_mul, U_coe_eq_uRaw_on_Icc hx]
  rw [intervalIntegral.integral_congr heq]
  have hcont_f : Continuous (fun x : ℝ => @fourier 2 (-n) (x : AddCircle (2 : ℝ))) := by
    simp_rw [fourier2_coe]; fun_prop
  have hsplit : ∫ x in (0 : ℝ)..2, @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * uRaw x =
      (∫ x in (0 : ℝ)..2, @fourier 2 (-n) (x : AddCircle (2 : ℝ))) -
      ∫ x in (1 : ℝ)..2, @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * (p6 (x - 3 / 2) : ℂ) := by
    have hi1 : IntervalIntegrable
        (fun x : ℝ => @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * uRaw x) volume 0 1 :=
      (hcont_f.mul uRaw_continuous).intervalIntegrable 0 1
    have hi2 : IntervalIntegrable
        (fun x : ℝ => @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * uRaw x) volume 1 2 :=
      (hcont_f.mul uRaw_continuous).intervalIntegrable 1 2
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    have hi_f1 : IntervalIntegrable
        (fun x : ℝ => @fourier 2 (-n) (x : AddCircle (2 : ℝ))) volume 0 1 :=
      hcont_f.intervalIntegrable 0 1
    have hi_f2 : IntervalIntegrable
        (fun x : ℝ => @fourier 2 (-n) (x : AddCircle (2 : ℝ))) volume 1 2 :=
      hcont_f.intervalIntegrable 1 2
    rw [← intervalIntegral.integral_add_adjacent_intervals hi_f1 hi_f2]
    have hpart1 : ∫ x in (0 : ℝ)..1, @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * uRaw x =
        ∫ x in (0 : ℝ)..1, @fourier 2 (-n) (x : AddCircle (2 : ℝ)) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      simp [uRaw, hx.2]
    have hpart2 : ∫ x in (1 : ℝ)..2, @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * uRaw x =
        (∫ x in (1 : ℝ)..2, @fourier 2 (-n) (x : AddCircle (2 : ℝ))) -
        ∫ x in (1 : ℝ)..2, @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * (p6 (x - 3 / 2) : ℂ) := by
      have hcongr : Set.EqOn
          (fun x : ℝ => @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * uRaw x)
          (fun x : ℝ => @fourier 2 (-n) (x : AddCircle (2 : ℝ)) -
            @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * (p6 (x - 3 / 2) : ℂ))
          (Set.uIcc 1 2) := by
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
        by_cases hx1 : x ≤ 1
        · have : x = 1 := le_antisymm hx1 hx.1
          subst this
          have hsub : (1 : ℝ) - 3 / 2 = -1 / 2 := by norm_num
          simp [uRaw, hsub, p6_end_neg]
        · simp [uRaw, hx1]; ring
      rw [intervalIntegral.integral_congr hcongr]
      exact intervalIntegral.integral_sub hi_f2
        (Continuous.intervalIntegrable (by unfold p6; fun_prop) 1 2)
    rw [hpart1, hpart2]; ring
  rw [hsplit, intervalIntegral_fourier2 (-n), if_neg (neg_ne_zero.mpr hn), zero_sub]
  have hshift : ∫ x in (1 : ℝ)..2, @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * (p6 (x - 3 / 2) : ℂ) =
      Complex.exp (-(Real.pi * Complex.I * (n : ℂ) * (3 / 2 : ℂ))) *
      ∫ t in (-1 / 2 : ℝ)..(1 / 2),
        (p6 t : ℂ) * Complex.exp (-(Real.pi * Complex.I * (n : ℂ) * (t : ℂ))) := by
    have hstep : ∀ x : ℝ,
        @fourier 2 (-n) (x : AddCircle (2 : ℝ)) * (p6 (x - 3 / 2) : ℂ) =
          Complex.exp (-(Real.pi * Complex.I * (n : ℂ) * (3 / 2 : ℂ))) *
          ((p6 (x - 3 / 2) : ℂ) *
            Complex.exp (-(Real.pi * Complex.I * (n : ℂ) * ((x - 3 / 2 : ℝ) : ℂ)))) := by
      intro x
      rw [fourier2_coe]
      have : Complex.exp (Real.pi * Complex.I * ((-n : ℤ) : ℂ) * (x : ℂ)) =
          Complex.exp (-(Real.pi * Complex.I * (n : ℂ) * (3 / 2 : ℂ))) *
          Complex.exp (-(Real.pi * Complex.I * (n : ℂ) * ((x - 3 / 2 : ℝ) : ℂ))) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [this]; ring
    simp_rw [hstep]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hcomp := intervalIntegral.integral_comp_sub_right
      (fun t : ℝ => (p6 t : ℂ) * Complex.exp (-(Real.pi * Complex.I * (n : ℂ) * (t : ℂ))))
      (3 / 2 : ℝ) (a := (1 : ℝ)) (b := 2)
    rw [show (1 : ℝ) - 3 / 2 = -1 / 2 by norm_num, show (2 : ℝ) - 3 / 2 = 1 / 2 by norm_num] at hcomp
    exact hcomp
  rw [hshift, integral_p6_mul_exp]
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), norm_neg, norm_mul]
  have hexp_norm : ‖Complex.exp (-(Real.pi * Complex.I * (n : ℂ) * (3 / 2 : ℂ)))‖ = 1 := by
    have : -(Real.pi * Complex.I * (n : ℂ) * (3 / 2 : ℂ)) =
        ((-(Real.pi * (n : ℝ) * (3 / 2)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  rw [hexp_norm, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hcos_abs :
      (fun t : ℝ => p6 t * Real.cos (Real.pi * (n : ℝ) * t)) =
      (fun t : ℝ => p6 t * Real.cos (Real.pi * (n.natAbs : ℝ) * t)) := by
    funext t
    rcases Int.natAbs_eq n with h | h
    · have hn' : (n : ℝ) = (n.natAbs : ℝ) := by conv_lhs => rw [h]; rw [Int.cast_natCast]
      rw [hn']
    · have hn' : (n : ℝ) = -(n.natAbs : ℝ) := by
        conv_lhs => rw [h]; rw [Int.cast_neg, Int.cast_natCast]
      rw [hn', show Real.pi * -(n.natAbs : ℝ) * t = -(Real.pi * (n.natAbs : ℝ) * t) by ring,
        Real.cos_neg]
  rw [hcos_abs]
  unfold pHat; ring

/- ## Exact closed-form evaluation of `pHat r` -/

private lemma integral_one_sub_pow6_cos (x : ℝ) (hx : x ≠ 0) :
    ∫ t in (-1 / 2 : ℝ)..(1 / 2), (1 - (2 * t) ^ 6) * Real.cos (x * t) =
      (240 / x ^ 3 - 11520 / x ^ 5 + 92160 / x ^ 7) * Real.sin (x / 2) +
      (-24 / x ^ 2 + 1920 / x ^ 4 - 46080 / x ^ 6) * Real.cos (x / 2) := by
  let A : ℝ → ℝ := fun t =>
    (1 - 64 * t ^ 6) / x + 1920 * t ^ 4 / x ^ 3 - 23040 * t ^ 2 / x ^ 5 + 46080 / x ^ 7
  let B : ℝ → ℝ := fun t =>
    -384 * t ^ 5 / x ^ 2 + 7680 * t ^ 3 / x ^ 4 - 46080 * t / x ^ 6
  let F : ℝ → ℝ := fun t => A t * Real.sin (x * t) + B t * Real.cos (x * t)
  have hderiv : ∀ t ∈ Set.uIcc (-1 / 2 : ℝ) (1 / 2),
      HasDerivAt F ((1 - (2 * t) ^ 6) * Real.cos (x * t)) t := by
    intro t _
    have hA : HasDerivAt A
        (-384 * t ^ 5 / x + 7680 * t ^ 3 / x ^ 3 - 46080 * t / x ^ 5) t := by
      have h1 : HasDerivAt (fun t : ℝ => (1 - 64 * t ^ 6) / x) (-384 * t ^ 5 / x) t :=
        ((((hasDerivAt_pow 6 t).const_mul (64 : ℝ)).const_sub (1 : ℝ)).div_const x).congr_deriv
          (by norm_num; ring)
      have h2 : HasDerivAt (fun t : ℝ => 1920 * t ^ 4 / x ^ 3) (7680 * t ^ 3 / x ^ 3) t :=
        (((hasDerivAt_pow 4 t).const_mul (1920 : ℝ)).div_const (x ^ 3)).congr_deriv
          (by norm_num; ring)
      have h3 : HasDerivAt (fun t : ℝ => 23040 * t ^ 2 / x ^ 5) (46080 * t / x ^ 5) t :=
        (((hasDerivAt_pow 2 t).const_mul (23040 : ℝ)).div_const (x ^ 5)).congr_deriv
          (by norm_num; ring)
      exact (((h1.add h2).sub h3).add (hasDerivAt_const t (46080 / x ^ 7))).congr_deriv (by ring)
    have hB : HasDerivAt B
        (-1920 * t ^ 4 / x ^ 2 + 23040 * t ^ 2 / x ^ 4 - 46080 / x ^ 6) t := by
      have h1 : HasDerivAt (fun t : ℝ => -384 * t ^ 5 / x ^ 2) (-1920 * t ^ 4 / x ^ 2) t :=
        (((hasDerivAt_pow 5 t).const_mul (-384 : ℝ)).div_const (x ^ 2)).congr_deriv
          (by norm_num; ring)
      have h2 : HasDerivAt (fun t : ℝ => 7680 * t ^ 3 / x ^ 4) (23040 * t ^ 2 / x ^ 4) t :=
        (((hasDerivAt_pow 3 t).const_mul (7680 : ℝ)).div_const (x ^ 4)).congr_deriv
          (by norm_num; ring)
      have h3 : HasDerivAt (fun t : ℝ => 46080 * t / x ^ 6) (46080 / x ^ 6) t :=
        (((hasDerivAt_id t).const_mul (46080 : ℝ)).div_const (x ^ 6)).congr_deriv (by ring)
      exact (h1.add h2).sub h3
    have hxt : HasDerivAt (fun t : ℝ => x * t) x t := by
      simpa using (hasDerivAt_id t).const_mul x
    have hsin : HasDerivAt (fun t : ℝ => Real.sin (x * t)) (Real.cos (x * t) * x) t :=
      (Real.hasDerivAt_sin (x * t)).comp t hxt
    have hcos : HasDerivAt (fun t : ℝ => Real.cos (x * t)) (-Real.sin (x * t) * x) t :=
      (Real.hasDerivAt_cos (x * t)).comp t hxt
    exact ((hA.mul hsin).add (hB.mul hcos)).congr_deriv (by
      dsimp only [A, B]
      field_simp [hx]
      ring)
  have hint : IntervalIntegrable (fun t : ℝ => (1 - (2 * t) ^ 6) * Real.cos (x * t))
      volume (-1 / 2) (1 / 2) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have h1 : x * (-1 / 2 : ℝ) = -(x / 2) := by ring
  have h2 : x * (1 / 2 : ℝ) = x / 2 := by ring
  dsimp only [F, A, B]
  rw [h1, h2, Real.sin_neg, Real.cos_neg]
  ring

private lemma pHat_even_eq (m : ℕ) (hm : 1 ≤ m) :
    pHat (2 * m) =
      56 / (Real.pi * (2 * m : ℝ)) ^ 2 -
      4480 / (Real.pi * (2 * m : ℝ)) ^ 4 +
      107520 / (Real.pi * (2 * m : ℝ)) ^ 6 := by
  have hx : Real.pi * ((2 * m : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (2 * m : ℕ) := by exact_mod_cast (by omega : 0 < 2 * m)
    exact mul_ne_zero Real.pi_ne_zero this.ne'
  unfold pHat p6
  have hmul : (fun t : ℝ => (7 / 3 : ℝ) * (1 - (2 * t) ^ 6) *
        Real.cos (Real.pi * ((2 * m : ℕ) : ℝ) * t)) =
      (fun t : ℝ => (7 / 3 : ℝ) * ((1 - (2 * t) ^ 6) *
        Real.cos (Real.pi * ((2 * m : ℕ) : ℝ) * t))) := by funext t; ring
  rw [hmul, intervalIntegral.integral_const_mul, integral_one_sub_pow6_cos _ hx]
  have harg : Real.pi * ((2 * m : ℕ) : ℝ) / 2 = (m : ℝ) * Real.pi := by push_cast; ring
  rw [harg, Real.sin_nat_mul_pi, mul_zero, zero_add, Real.cos_nat_mul_pi]
  have hcast : ((2 * m : ℕ) : ℝ) = (2 * m : ℝ) := by push_cast; ring
  rw [hcast]
  set x : ℝ := Real.pi * (2 * m : ℝ)
  have hxpos : 0 < x := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have hval_pos : 0 < 56 / x ^ 2 - 4480 / x ^ 4 + 107520 / x ^ 6 := by
    have hfac : 56 / x ^ 2 - 4480 / x ^ 4 + 107520 / x ^ 6 =
        56 * ((x ^ 2 - 40) ^ 2 + 320) / x ^ 6 := by field_simp [hxpos.ne']; ring
    rw [hfac]
    have hnum : 0 < 56 * ((x ^ 2 - 40) ^ 2 + 320) := by nlinarith [sq_nonneg (x ^ 2 - 40)]
    exact div_pos hnum (pow_pos hxpos 6)
  have hrew : (7 / 3 : ℝ) * ((-24 / x ^ 2 + 1920 / x ^ 4 - 46080 / x ^ 6) * (-1) ^ m) =
      -((-1) ^ m * (56 / x ^ 2 - 4480 / x ^ 4 + 107520 / x ^ 6)) := by ring
  rw [hrew, abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hval_pos]

private lemma pHat_odd_eq (k : ℕ) :
    pHat (2 * k + 1) =
      560 / (Real.pi * (2 * k + 1 : ℝ)) ^ 3 -
      26880 / (Real.pi * (2 * k + 1 : ℝ)) ^ 5 +
      215040 / (Real.pi * (2 * k + 1 : ℝ)) ^ 7 := by
  have hx : Real.pi * ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (2 * k + 1 : ℕ) := by exact_mod_cast (Nat.succ_pos (2 * k))
    exact mul_ne_zero Real.pi_ne_zero this.ne'
  unfold pHat p6
  have hmul : (fun t : ℝ => (7 / 3 : ℝ) * (1 - (2 * t) ^ 6) *
        Real.cos (Real.pi * ((2 * k + 1 : ℕ) : ℝ) * t)) =
      (fun t : ℝ => (7 / 3 : ℝ) * ((1 - (2 * t) ^ 6) *
        Real.cos (Real.pi * ((2 * k + 1 : ℕ) : ℝ) * t))) := by funext t; ring
  rw [hmul, intervalIntegral.integral_const_mul, integral_one_sub_pow6_cos _ hx]
  have harg : Real.pi * ((2 * k + 1 : ℕ) : ℝ) / 2 = (k : ℝ) * Real.pi + Real.pi / 2 := by
    push_cast; ring
  rw [harg, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two,
    Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, neg_zero, mul_zero, add_zero]
  have hcast : ((2 * k + 1 : ℕ) : ℝ) = (2 * k + 1 : ℝ) := by push_cast; ring
  rw [hcast]
  set x : ℝ := Real.pi * (2 * k + 1 : ℝ)
  have hxpos : 0 < x := by
    have : (0 : ℝ) < 2 * k + 1 := by positivity
    exact mul_pos Real.pi_pos this
  have hval_pos : 0 < 560 / x ^ 3 - 26880 / x ^ 5 + 215040 / x ^ 7 := by
    have hfac : 560 / x ^ 3 - 26880 / x ^ 5 + 215040 / x ^ 7 =
        560 * ((x ^ 2 - 24) ^ 2 - 192) / x ^ 7 := by field_simp [hxpos.ne']; ring
    rw [hfac]
    have hpi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
    have hpi_hi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
    have hquad : 0 < (x ^ 2 - 24) ^ 2 - 192 := by
      rcases k with _ | k'
      · have hx_eq : x = Real.pi := by simp [x]
        rw [hx_eq]
        nlinarith [sq_nonneg (Real.pi - 3.141593)]
      · have hx_ge : 3 * Real.pi ≤ x := by
          have hk1 : (3 : ℝ) ≤ 2 * (k' + 1 : ℕ) + 1 := by push_cast; linarith
          have : 3 * Real.pi ≤ Real.pi * (2 * (k' + 1 : ℕ) + 1) := by nlinarith [Real.pi_pos]
          simpa [x] using this
        have hx2 : (80 : ℝ) ≤ x ^ 2 := by nlinarith [Real.pi_pos]
        nlinarith
    exact div_pos (by positivity) (pow_pos hxpos 7)
  have hrew : (7 / 3 : ℝ) * ((240 / x ^ 3 - 11520 / x ^ 5 + 92160 / x ^ 7) * (-1) ^ k) =
      (-1) ^ k * (560 / x ^ 3 - 26880 / x ^ 5 + 215040 / x ^ 7) := by ring
  rw [hrew, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hval_pos]

private lemma pHat_even_le_main (m : ℕ) (hm : 1 ≤ m) :
    pHat (2 * m) ≤ 14 / (Real.pi ^ 2 * (m : ℝ) ^ 2) := by
  rw [pHat_even_eq m hm]
  set x : ℝ := Real.pi * (2 * m : ℝ)
  have hm_pos : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx_ge : 6 ≤ x := by
    have := Real.pi_gt_d6
    nlinarith
  have hx_pos : 0 < x := by linarith
  have htail : 107520 / x ^ 6 ≤ 4480 / x ^ 4 := by
    rw [div_le_div_iff₀ (pow_pos hx_pos 6) (pow_pos hx_pos 4)]
    have h24 : (24 : ℝ) ≤ x ^ 2 := by nlinarith
    have h4 : (0 : ℝ) < x ^ 4 := pow_pos hx_pos 4
    nlinarith
  have hlead : 56 / x ^ 2 = 14 / (Real.pi ^ 2 * (m : ℝ) ^ 2) := by
    simp only [x]; field_simp [Real.pi_ne_zero, (by linarith : (m : ℝ) ≠ 0)]; ring
  linarith

private lemma pHat_odd_le_main (k : ℕ) :
    pHat (2 * k + 1) ≤ 560 / (Real.pi ^ 3 * (2 * k + 1 : ℝ) ^ 3) := by
  rw [pHat_odd_eq k]
  set x : ℝ := Real.pi * (2 * k + 1 : ℝ)
  have hx_ge : 3 ≤ x := by
    have := Real.pi_gt_d6
    have hk : (1 : ℝ) ≤ 2 * k + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    nlinarith
  have hx_pos : 0 < x := by linarith
  have htail : 215040 / x ^ 7 ≤ 26880 / x ^ 5 := by
    rw [div_le_div_iff₀ (pow_pos hx_pos 7) (pow_pos hx_pos 5)]
    have h8 : (8 : ℝ) ≤ x ^ 2 := by nlinarith
    have h5 : (0 : ℝ) < x ^ 5 := pow_pos hx_pos 5
    nlinarith
  have hlead : 560 / x ^ 3 = 560 / (Real.pi ^ 3 * (2 * k + 1 : ℝ) ^ 3) := by
    simp only [x]; ring
  linarith

private lemma pHat_le_sixty_div_sq (r : ℕ) (hr : 1 ≤ r) :
    pHat r ≤ 60 / (r : ℝ) ^ 2 := by
  have hpi : (3 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d6]
  have hpi2 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
  have hpi3 : (27 : ℝ) ≤ Real.pi ^ 3 := by nlinarith
  rcases Nat.even_or_odd r with ⟨m, rfl⟩ | ⟨k, rfl⟩
  · have hm : 1 ≤ m := by omega
    have h := pHat_even_le_main m hm
    rw [show m + m = 2 * m by omega]
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
    calc pHat (2 * m) ≤ 14 / (Real.pi ^ 2 * (m : ℝ) ^ 2) := h
      _ ≤ 60 / ((2 * m : ℕ) : ℝ) ^ 2 := by
        push_cast
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := sq_pos_of_pos hm_pos
        nlinarith
  · have h := pHat_odd_le_main k
    have hk_ge : (1 : ℝ) ≤ 2 * k + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    calc pHat (2 * k + 1) ≤ 560 / (Real.pi ^ 3 * (2 * k + 1 : ℝ) ^ 3) := h
      _ ≤ 60 / ((2 * k + 1 : ℕ) : ℝ) ^ 2 := by
        push_cast
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h2 : (0 : ℝ) < (2 * (k : ℝ) + 1) ^ 2 := by positivity
        have h3 : (2 * (k : ℝ) + 1) ^ 2 ≤ (2 * (k : ℝ) + 1) ^ 3 := by nlinarith
        nlinarith

private lemma summable_fourierCoeff_U : Summable (fourierCoeff U) := by
  refine Summable.of_norm ?_
  have hnat : Summable (fun n : ℕ => ‖fourierCoeff U n‖) := by
    have hdom : Summable (fun n : ℕ => (30 : ℝ) * (1 / (n : ℝ) ^ 2)) :=
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left 30
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hdom
    intro n
    rcases n with _ | n
    · simp [fourierCoeff_U_zero]
    · rw [norm_fourierCoeff_U (n + 1 : ℕ) (by positivity)]
      have hle := pHat_le_sixty_div_sq (n + 1) (by omega)
      have habs : ((n + 1 : ℕ) : ℤ).natAbs = n + 1 := Int.natAbs_natCast (n + 1)
      rw [habs]
      have heq : 60 / ((n + 1 : ℕ) : ℝ) ^ 2 / 2 = 30 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by ring
      linarith
  have hneg : Summable (fun n : ℕ => ‖fourierCoeff U (-((n : ℤ) + 1))‖) := by
    have heq : (fun n : ℕ => ‖fourierCoeff U (-((n : ℤ) + 1))‖) =
        (fun n : ℕ => ‖fourierCoeff U ((n + 1 : ℕ) : ℤ)‖) := by
      funext n
      rw [norm_fourierCoeff_U (-((n : ℤ) + 1)) (by omega),
        norm_fourierCoeff_U ((n + 1 : ℕ) : ℤ) (by omega)]
      congr 2
    rw [heq]
    exact hnat.comp_injective Nat.succ_injective
  exact Summable.of_nat_of_neg_add_one hnat hneg

private lemma summable_pHat_rpow : Summable (fun r : ℕ => pHat (r + 1) ^ (4 / 3 : ℝ)) := by
  have hdom : Summable (fun r : ℕ => (60 : ℝ) ^ (4 / 3 : ℝ) * (1 / ((r + 1 : ℕ) : ℝ) ^ 2)) := by
    have h1 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    exact (h1.comp_injective Nat.succ_injective).mul_left _
  refine Summable.of_nonneg_of_le (fun r => Real.rpow_nonneg (abs_nonneg _) _) ?_ hdom
  intro r
  have hr1 : (1 : ℝ) ≤ (r + 1 : ℕ) := by exact_mod_cast (Nat.succ_pos r)
  have hle := pHat_le_sixty_div_sq (r + 1) (Nat.succ_pos r)
  calc pHat (r + 1) ^ (4 / 3 : ℝ)
      ≤ (60 / ((r + 1 : ℕ) : ℝ) ^ 2) ^ (4 / 3 : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg _) hle (by norm_num)
    _ = 60 ^ (4 / 3 : ℝ) * (1 / ((r + 1 : ℕ) : ℝ) ^ 2) ^ (4 / 3 : ℝ) := by
        rw [div_eq_mul_inv, Real.mul_rpow (by norm_num) (by positivity), one_div]
    _ ≤ 60 ^ (4 / 3 : ℝ) * (1 / ((r + 1 : ℕ) : ℝ) ^ 2) := by
        gcongr
        have hu1 : (1 : ℝ) / ((r + 1 : ℕ) : ℝ) ^ 2 ≤ 1 := by
          rw [div_le_one (by positivity)]; nlinarith
        exact Real.rpow_le_self_of_le_one (by positivity) hu1 (by norm_num)

/- ## Exact 20-term rational bound and telescoping tail bounds for `∑' r, pHat (r + 1) ^ (4/3)` -/

private lemma rpow_four_thirds_le {x q : ℝ} (hx : 0 ≤ x) (hq : 0 ≤ q) (h : x ^ 4 ≤ q ^ 3) :
    x ^ (4 / 3 : ℝ) ≤ q := by
  have h3 : (x ^ (4 / 3 : ℝ)) ^ (3 : ℕ) ≤ q ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast (x ^ (4 / 3 : ℝ)) 3, ← Real.rpow_mul hx]
    norm_num
    exact h
  exact le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hq h3

private lemma pHat_even_rpow_le (m : ℕ) (hm : 1 ≤ m) (q : ℝ) (hq : 0 ≤ q)
    (hnum : (56 / (3.141592 * (2 * m : ℝ)) ^ 2 -
      4480 / (3.141593 * (2 * m : ℝ)) ^ 4 +
      107520 / (3.141592 * (2 * m : ℝ)) ^ 6) ^ 4 ≤ q ^ 3) :
    pHat (2 * m) ^ (4 / 3 : ℝ) ≤ q := by
  refine rpow_four_thirds_le (abs_nonneg _) hq ?_
  have hpi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi_hi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  have hm_pos : (0 : ℝ) < 2 * m := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have h1 : 56 / (Real.pi * (2 * m : ℝ)) ^ 2 ≤ 56 / (3.141592 * (2 * m : ℝ)) ^ 2 := by
    gcongr
  have h2 : 4480 / (3.141593 * (2 * m : ℝ)) ^ 4 ≤ 4480 / (Real.pi * (2 * m : ℝ)) ^ 4 := by
    gcongr
  have h3 : 107520 / (Real.pi * (2 * m : ℝ)) ^ 6 ≤ 107520 / (3.141592 * (2 * m : ℝ)) ^ 6 := by
    gcongr
  have hle : pHat (2 * m) ≤ 56 / (3.141592 * (2 * m : ℝ)) ^ 2 -
      4480 / (3.141593 * (2 * m : ℝ)) ^ 4 +
      107520 / (3.141592 * (2 * m : ℝ)) ^ 6 := by
    rw [pHat_even_eq m hm]; linarith
  exact le_trans (pow_le_pow_left₀ (abs_nonneg _) hle 4) hnum

private lemma pHat_odd_rpow_le (k : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hnum : (560 / (3.141592 * (2 * k + 1 : ℝ)) ^ 3 -
      26880 / (3.141593 * (2 * k + 1 : ℝ)) ^ 5 +
      215040 / (3.141592 * (2 * k + 1 : ℝ)) ^ 7) ^ 4 ≤ q ^ 3) :
    pHat (2 * k + 1) ^ (4 / 3 : ℝ) ≤ q := by
  refine rpow_four_thirds_le (abs_nonneg _) hq ?_
  have hpi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi_hi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  have hk_pos : (0 : ℝ) < 2 * k + 1 := by positivity
  have h1 : 560 / (Real.pi * (2 * k + 1 : ℝ)) ^ 3 ≤
      560 / (3.141592 * (2 * k + 1 : ℝ)) ^ 3 := by gcongr
  have h2 : 26880 / (3.141593 * (2 * k + 1 : ℝ)) ^ 5 ≤
      26880 / (Real.pi * (2 * k + 1 : ℝ)) ^ 5 := by gcongr
  have h3 : 215040 / (Real.pi * (2 * k + 1 : ℝ)) ^ 7 ≤
      215040 / (3.141592 * (2 * k + 1 : ℝ)) ^ 7 := by gcongr
  have hle : pHat (2 * k + 1) ≤ 560 / (3.141592 * (2 * k + 1 : ℝ)) ^ 3 -
      26880 / (3.141593 * (2 * k + 1 : ℝ)) ^ 5 +
      215040 / (3.141592 * (2 * k + 1 : ℝ)) ^ 7 := by
    rw [pHat_odd_eq k]; linarith
  exact le_trans (pow_le_pow_left₀ (abs_nonneg _) hle 4) hnum

private lemma rpow_neg_eight_thirds_le_diff (x : ℝ) (hx : 1 < x) :
    x ^ (-8 / 3 : ℝ) ≤ (3 / 5 : ℝ) * ((x - 1) ^ (-5 / 3 : ℝ) - x ^ (-5 / 3 : ℝ)) := by
  have hx0 : 0 < x - 1 := by linarith
  have hx1 : 0 < x := by linarith
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-5 / 3 : ℝ)) (Set.Icc (x - 1) x) :=
    ContinuousOn.rpow_const continuousOn_id (fun t ht => Or.inl (by linarith [ht.1]))
  have hdiff : ∀ t ∈ Set.Ioo (x - 1) x,
      HasDerivAt (fun t : ℝ => t ^ (-5 / 3 : ℝ)) ((-5 / 3 : ℝ) * t ^ (-8 / 3 : ℝ)) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have h := (hasDerivAt_id t).rpow_const (p := (-5 / 3 : ℝ)) (Or.inl ht0)
    convert h using 1; simp only [id_eq]; norm_num
  obtain ⟨c, ⟨hc1, hc2⟩, hslope⟩ :=
    exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (-5 / 3 : ℝ)) _ (by linarith : x - 1 < x)
      hcont hdiff
  have hc0 : 0 < c := by linarith
  have hsub : x - (x - 1) = 1 := by ring
  rw [hsub, div_one] at hslope
  have hmono : x ^ (-8 / 3 : ℝ) ≤ c ^ (-8 / 3 : ℝ) := by
    rw [show (-8 / 3 : ℝ) = -(8 / 3) by norm_num, Real.rpow_neg hx1.le, Real.rpow_neg hc0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hc0 _)
      (Real.rpow_le_rpow hc0.le hc2.le (by norm_num))
  linarith

private lemma inv_pow4_le_diff_pow3 (r : ℝ) (hr : 2 < r) :
    1 / r ^ 4 ≤ (1 / 6 : ℝ) * (1 / (r - 2) ^ 3 - 1 / r ^ 3) := by
  have hr0 : 0 < r := by linarith
  have hr2 : 0 < r - 2 := by linarith
  have h1 : 1 / (r - 2) ^ 3 - 1 / r ^ 3 = (6 * r ^ 2 - 12 * r + 8) / ((r - 2) ^ 3 * r ^ 3) := by
    field_simp [hr0.ne', hr2.ne']; ring
  rw [h1]
  have h2 : 1 / r ^ 4 ≤ (1 / 6 : ℝ) * ((6 * r ^ 2 - 12 * r + 8) / ((r - 2) ^ 3 * r ^ 3)) := by
    have hden : 0 < 6 * ((r - 2) ^ 3 * r ^ 3) := by positivity
    rw [show (1 / 6 : ℝ) * ((6 * r ^ 2 - 12 * r + 8) / ((r - 2) ^ 3 * r ^ 3)) =
        (6 * r ^ 2 - 12 * r + 8) / (6 * ((r - 2) ^ 3 * r ^ 3)) by field_simp [hr0.ne', hr2.ne']]
    rw [div_le_div_iff₀ (pow_pos hr0 4) hden]
    have hpoly : (6 * r ^ 2 - 12 * r + 8) * r ^ 4 - 6 * ((r - 2) ^ 3 * r ^ 3) =
        r ^ 3 * (24 * r ^ 2 - 64 * r + 48) := by ring
    have hpos : 0 ≤ 24 * r ^ 2 - 64 * r + 48 := by nlinarith
    have hpos2 : 0 ≤ r ^ 3 * (24 * r ^ 2 - 64 * r + 48) := mul_nonneg (by positivity) hpos
    linarith
  exact h2

private lemma sum_pHat_head_le :
    ∑ r ∈ Finset.range 20, pHat (r + 1) ^ (4 / 3 : ℝ) ≤ 11933 / 5000 := by
  have h1 : pHat 1 ^ (4 / 3 : ℝ) ≤ 15990 / 10000 :=
    pHat_odd_rpow_le 0 _ (by norm_num) (by norm_num)
  have h2 : pHat 2 ^ (4 / 3 : ℝ) ≤ 1933 / 10000 :=
    pHat_even_rpow_le 1 (by omega) _ (by norm_num) (by norm_num)
  have h3 : pHat 3 ^ (4 / 3 : ℝ) ≤ 2374 / 10000 :=
    pHat_odd_rpow_le 1 _ (by norm_num) (by norm_num)
  have h4 : pHat 4 ^ (4 / 3 : ℝ) ≤ 1188 / 10000 :=
    pHat_even_rpow_le 2 (by omega) _ (by norm_num) (by norm_num)
  have h5 : pHat 5 ^ (4 / 3 : ℝ) ≤ 575 / 10000 :=
    pHat_odd_rpow_le 2 _ (by norm_num) (by norm_num)
  have h6 : pHat 6 ^ (4 / 3 : ℝ) ≤ 622 / 10000 :=
    pHat_even_rpow_le 3 (by omega) _ (by norm_num) (by norm_num)
  have h7 : pHat 7 ^ (4 / 3 : ℝ) ≤ 173 / 10000 :=
    pHat_odd_rpow_le 3 _ (by norm_num) (by norm_num)
  have h8 : pHat 8 ^ (4 / 3 : ℝ) ≤ 333 / 10000 :=
    pHat_even_rpow_le 4 (by omega) _ (by norm_num) (by norm_num)
  have h9 : pHat 9 ^ (4 / 3 : ℝ) ≤ 67 / 10000 :=
    pHat_odd_rpow_le 4 _ (by norm_num) (by norm_num)
  have h10 : pHat 10 ^ (4 / 3 : ℝ) ≤ 196 / 10000 :=
    pHat_even_rpow_le 5 (by omega) _ (by norm_num) (by norm_num)
  have h11 : pHat 11 ^ (4 / 3 : ℝ) ≤ 31 / 10000 :=
    pHat_odd_rpow_le 5 _ (by norm_num) (by norm_num)
  have h12 : pHat 12 ^ (4 / 3 : ℝ) ≤ 125 / 10000 :=
    pHat_even_rpow_le 6 (by omega) _ (by norm_num) (by norm_num)
  have h13 : pHat 13 ^ (4 / 3 : ℝ) ≤ 16 / 10000 :=
    pHat_odd_rpow_le 6 _ (by norm_num) (by norm_num)
  have h14 : pHat 14 ^ (4 / 3 : ℝ) ≤ 85 / 10000 :=
    pHat_even_rpow_le 7 (by omega) _ (by norm_num) (by norm_num)
  have h15 : pHat 15 ^ (4 / 3 : ℝ) ≤ 10 / 10000 :=
    pHat_odd_rpow_le 7 _ (by norm_num) (by norm_num)
  have h16 : pHat 16 ^ (4 / 3 : ℝ) ≤ 60 / 10000 :=
    pHat_even_rpow_le 8 (by omega) _ (by norm_num) (by norm_num)
  have h17 : pHat 17 ^ (4 / 3 : ℝ) ≤ 6 / 10000 :=
    pHat_odd_rpow_le 8 _ (by norm_num) (by norm_num)
  have h18 : pHat 18 ^ (4 / 3 : ℝ) ≤ 44 / 10000 :=
    pHat_even_rpow_le 9 (by omega) _ (by norm_num) (by norm_num)
  have h19 : pHat 19 ^ (4 / 3 : ℝ) ≤ 4 / 10000 :=
    pHat_odd_rpow_le 9 _ (by norm_num) (by norm_num)
  have h20 : pHat 20 ^ (4 / 3 : ℝ) ≤ 34 / 10000 :=
    pHat_even_rpow_le 10 (by omega) _ (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  linarith

private lemma tsum_pHat_tail_le :
    ∑' k : ℕ, pHat (k + 21) ^ (4 / 3 : ℝ) ≤ 207 / 10000 + 1 / 500 := by
  have hs : Summable (fun k : ℕ => pHat (k + 21) ^ (4 / 3 : ℝ)) := by
    have := summable_pHat_rpow.comp_injective (add_left_injective 20)
    simpa [Function.comp_def, add_assoc] using this
  refine hs.tsum_le_of_sum_range_le ?_
  intro N
  have hsplit : ∑ k ∈ Finset.range N, pHat (k + 21) ^ (4 / 3 : ℝ) ≤
      (∑ m ∈ Finset.range N, pHat (2 * (m + 11)) ^ (4 / 3 : ℝ)) +
      (∑ m ∈ Finset.range N, pHat (2 * m + 21) ^ (4 / 3 : ℝ)) := by
    have hsub : Finset.range N ⊆
        (Finset.range N).image (fun m => 2 * m + 1) ∪ (Finset.range N).image (fun m => 2 * m) := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
      rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · right; exact ⟨m, Finset.mem_range.mpr (by omega), by omega⟩
      · left; exact ⟨m, Finset.mem_range.mpr (by omega), by omega⟩
    have hdisj : Disjoint ((Finset.range N).image (fun m => 2 * m + 1))
        ((Finset.range N).image (fun m => 2 * m)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_image] at hx1 hx2
      obtain ⟨a, _, rfl⟩ := hx1
      obtain ⟨b, _, hb⟩ := hx2
      omega
    calc ∑ k ∈ Finset.range N, pHat (k + 21) ^ (4 / 3 : ℝ)
        ≤ ∑ k ∈ (Finset.range N).image (fun m => 2 * m + 1) ∪
            (Finset.range N).image (fun m => 2 * m), pHat (k + 21) ^ (4 / 3 : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun _ _ _ => Real.rpow_nonneg (abs_nonneg _) _)
      _ = (∑ k ∈ (Finset.range N).image (fun m => 2 * m + 1), pHat (k + 21) ^ (4 / 3 : ℝ)) +
          (∑ k ∈ (Finset.range N).image (fun m => 2 * m), pHat (k + 21) ^ (4 / 3 : ℝ)) :=
          Finset.sum_union hdisj
      _ = (∑ m ∈ Finset.range N, pHat (2 * (m + 11)) ^ (4 / 3 : ℝ)) +
          (∑ m ∈ Finset.range N, pHat (2 * m + 21) ^ (4 / 3 : ℝ)) := by
          congr 1
          · rw [Finset.sum_image (by intro a _ b _ h; dsimp at h; omega)]
            refine Finset.sum_congr rfl fun m _ => ?_
            congr 1
          · rw [Finset.sum_image (by intro a _ b _ h; dsimp at h; omega)]
  have heven : ∑ m ∈ Finset.range N, pHat (2 * (m + 11)) ^ (4 / 3 : ℝ) ≤ 207 / 10000 := by
    have hterm : ∀ m ∈ Finset.range N,
        pHat (2 * (m + 11)) ^ (4 / 3 : ℝ) ≤
          (14 / Real.pi ^ 2) ^ (4 / 3 : ℝ) * (3 / 5 : ℝ) *
            (((m + 10 : ℕ) : ℝ) ^ (-5 / 3 : ℝ) - ((m + 11 : ℕ) : ℝ) ^ (-5 / 3 : ℝ)) := by
      intro m _
      have h1 := pHat_even_le_main (m + 11) (by omega)
      have hm_pos : (0 : ℝ) < ((m + 11 : ℕ) : ℝ) := by positivity
      have h2 : pHat (2 * (m + 11)) ^ (4 / 3 : ℝ) ≤
          (14 / Real.pi ^ 2) ^ (4 / 3 : ℝ) * ((m + 11 : ℕ) : ℝ) ^ (-8 / 3 : ℝ) := by
        calc pHat (2 * (m + 11)) ^ (4 / 3 : ℝ)
            ≤ (14 / (Real.pi ^ 2 * ((m + 11 : ℕ) : ℝ) ^ 2)) ^ (4 / 3 : ℝ) :=
              Real.rpow_le_rpow (abs_nonneg _) h1 (by norm_num)
          _ = ((14 / Real.pi ^ 2) * (((m + 11 : ℕ) : ℝ) ^ (-2 : ℝ))) ^ (4 / 3 : ℝ) := by
              congr 1
              rw [Real.rpow_neg hm_pos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
                Real.rpow_natCast]
              ring
          _ = (14 / Real.pi ^ 2) ^ (4 / 3 : ℝ) * ((m + 11 : ℕ) : ℝ) ^ (-8 / 3 : ℝ) := by
              rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hm_pos.le _),
                ← Real.rpow_mul hm_pos.le]
              norm_num
      have h3 := rpow_neg_eight_thirds_le_diff ((m + 11 : ℕ) : ℝ)
        (by exact_mod_cast (by omega : 1 < m + 11))
      have hsub : ((m + 11 : ℕ) : ℝ) - 1 = ((m + 10 : ℕ) : ℝ) := by push_cast; ring
      rw [hsub] at h3
      have hC : 0 ≤ (14 / Real.pi ^ 2) ^ (4 / 3 : ℝ) := Real.rpow_nonneg (by positivity) _
      calc pHat (2 * (m + 11)) ^ (4 / 3 : ℝ)
          ≤ (14 / Real.pi ^ 2) ^ (4 / 3 : ℝ) * ((m + 11 : ℕ) : ℝ) ^ (-8 / 3 : ℝ) := h2
        _ ≤ (14 / Real.pi ^ 2) ^ (4 / 3 : ℝ) *
            ((3 / 5 : ℝ) * (((m + 10 : ℕ) : ℝ) ^ (-5 / 3 : ℝ) -
              ((m + 11 : ℕ) : ℝ) ^ (-5 / 3 : ℝ))) :=
            mul_le_mul_of_nonneg_left h3 hC
        _ = (14 / Real.pi ^ 2) ^ (4 / 3 : ℝ) * (3 / 5 : ℝ) *
            (((m + 10 : ℕ) : ℝ) ^ (-5 / 3 : ℝ) - ((m + 11 : ℕ) : ℝ) ^ (-5 / 3 : ℝ)) := by ring
    calc ∑ m ∈ Finset.range N, pHat (2 * (m + 11)) ^ (4 / 3 : ℝ)
        ≤ ∑ m ∈ Finset.range N, (14 / Real.pi ^ 2) ^ (4 / 3 : ℝ) * (3 / 5 : ℝ) *
            (((m + 10 : ℕ) : ℝ) ^ (-5 / 3 : ℝ) - ((m + 11 : ℕ) : ℝ) ^ (-5 / 3 : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = (14 / Real.pi ^ 2) ^ (4 / 3 : ℝ) * (3 / 5 : ℝ) *
            ∑ m ∈ Finset.range N,
              (((m + 10 : ℕ) : ℝ) ^ (-5 / 3 : ℝ) - ((m + 11 : ℕ) : ℝ) ^ (-5 / 3 : ℝ)) := by
          rw [Finset.mul_sum]
      _ = (14 / Real.pi ^ 2) ^ (4 / 3 : ℝ) * (3 / 5 : ℝ) *
            (((10 : ℝ) ^ (-5 / 3 : ℝ)) - ((N + 10 : ℕ) : ℝ) ^ (-5 / 3 : ℝ)) := by
          congr 1
          have htel := Finset.sum_range_sub' (fun m : ℕ => ((m + 10 : ℕ) : ℝ) ^ (-5 / 3 : ℝ)) N
          have heq : (fun m : ℕ => ((m + 10 : ℕ) : ℝ) ^ (-5 / 3 : ℝ) -
              (((m + 1) + 10 : ℕ) : ℝ) ^ (-5 / 3 : ℝ)) =
            (fun m : ℕ => ((m + 10 : ℕ) : ℝ) ^ (-5 / 3 : ℝ) -
              ((m + 11 : ℕ) : ℝ) ^ (-5 / 3 : ℝ)) := by
            funext m; simp only [add_assoc]
          rw [heq] at htel
          simpa using htel
      _ ≤ (14 / Real.pi ^ 2) ^ (4 / 3 : ℝ) * (3 / 5 : ℝ) * (10 : ℝ) ^ (-5 / 3 : ℝ) := by
          have hC : 0 ≤ (14 / Real.pi ^ 2) ^ (4 / 3 : ℝ) * (3 / 5 : ℝ) := by positivity
          have hnn : 0 ≤ ((N + 10 : ℕ) : ℝ) ^ (-5 / 3 : ℝ) :=
            Real.rpow_nonneg (by positivity) _
          nlinarith
      _ ≤ 207 / 10000 := by
          have hpi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
          have hle1 : (14 / Real.pi ^ 2) ^ (4 / 3 : ℝ) * (3 / 5 : ℝ) * (10 : ℝ) ^ (-5 / 3 : ℝ) ≤
              (14 / (3.141592 : ℝ) ^ 2) ^ (4 / 3 : ℝ) * (3 / 5 : ℝ) * (10 : ℝ) ^ (-5 / 3 : ℝ) := by
            gcongr
          refine le_trans hle1 ?_
          have h3 : ((14 / (3.141592 : ℝ) ^ 2) ^ (4 / 3 : ℝ) * (3 / 5 : ℝ) *
              (10 : ℝ) ^ (-5 / 3 : ℝ)) ^ (3 : ℕ) ≤ (207 / 10000 : ℝ) ^ (3 : ℕ) := by
            rw [mul_pow, mul_pow,
              ← Real.rpow_natCast ((14 / (3.141592 : ℝ) ^ 2) ^ (4 / 3 : ℝ)) 3,
              ← Real.rpow_mul (by norm_num),
              ← Real.rpow_natCast ((10 : ℝ) ^ (-5 / 3 : ℝ)) 3,
              ← Real.rpow_mul (by norm_num)]
            norm_num
          exact le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by norm_num) h3
  have hodd : ∑ m ∈ Finset.range N, pHat (2 * m + 21) ^ (4 / 3 : ℝ) ≤ 1 / 500 := by
    have hterm : ∀ m ∈ Finset.range N,
        pHat (2 * m + 21) ^ (4 / 3 : ℝ) ≤
          (560 / Real.pi ^ 3) ^ (4 / 3 : ℝ) * (1 / 6 : ℝ) *
            (1 / (2 * (m : ℝ) + 19) ^ 3 - 1 / (2 * (m : ℝ) + 21) ^ 3) := by
      intro m _
      have h1 := pHat_odd_le_main (m + 10)
      have hr_eq : 2 * (m + 10) + 1 = 2 * m + 21 := by omega
      rw [hr_eq] at h1
      have hcast : (2 * ((m + 10 : ℕ) : ℝ) + 1) = 2 * (m : ℝ) + 21 := by push_cast; ring
      rw [hcast] at h1
      have hr_pos : (0 : ℝ) < 2 * (m : ℝ) + 21 := by positivity
      have h2 : pHat (2 * m + 21) ^ (4 / 3 : ℝ) ≤
          (560 / Real.pi ^ 3) ^ (4 / 3 : ℝ) * (1 / (2 * (m : ℝ) + 21) ^ 4) := by
        calc pHat (2 * m + 21) ^ (4 / 3 : ℝ)
            ≤ (560 / (Real.pi ^ 3 * (2 * (m : ℝ) + 21) ^ 3)) ^ (4 / 3 : ℝ) :=
              Real.rpow_le_rpow (abs_nonneg _) h1 (by norm_num)
          _ = ((560 / Real.pi ^ 3) * ((2 * (m : ℝ) + 21) ^ (-3 : ℝ))) ^ (4 / 3 : ℝ) := by
              congr 1
              rw [Real.rpow_neg hr_pos.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
                Real.rpow_natCast]
              field_simp [Real.pi_ne_zero, hr_pos.ne']
          _ = (560 / Real.pi ^ 3) ^ (4 / 3 : ℝ) * (1 / (2 * (m : ℝ) + 21) ^ 4) := by
              rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hr_pos.le _),
                ← Real.rpow_mul hr_pos.le]
              rw [show (-3 : ℝ) * (4 / 3 : ℝ) = -(4 : ℝ) by norm_num, Real.rpow_neg hr_pos.le,
                show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
      have h3 := inv_pow4_le_diff_pow3 (2 * (m : ℝ) + 21) (by linarith [Nat.cast_nonneg (α := ℝ) m])
      have hsub : 2 * (m : ℝ) + 21 - 2 = 2 * (m : ℝ) + 19 := by ring
      rw [hsub] at h3
      have hC : 0 ≤ (560 / Real.pi ^ 3) ^ (4 / 3 : ℝ) := Real.rpow_nonneg (by positivity) _
      calc pHat (2 * m + 21) ^ (4 / 3 : ℝ)
          ≤ (560 / Real.pi ^ 3) ^ (4 / 3 : ℝ) * (1 / (2 * (m : ℝ) + 21) ^ 4) := h2
        _ ≤ (560 / Real.pi ^ 3) ^ (4 / 3 : ℝ) *
            ((1 / 6 : ℝ) * (1 / (2 * (m : ℝ) + 19) ^ 3 - 1 / (2 * (m : ℝ) + 21) ^ 3)) :=
            mul_le_mul_of_nonneg_left h3 hC
        _ = (560 / Real.pi ^ 3) ^ (4 / 3 : ℝ) * (1 / 6 : ℝ) *
            (1 / (2 * (m : ℝ) + 19) ^ 3 - 1 / (2 * (m : ℝ) + 21) ^ 3) := by ring
    calc ∑ m ∈ Finset.range N, pHat (2 * m + 21) ^ (4 / 3 : ℝ)
        ≤ ∑ m ∈ Finset.range N, (560 / Real.pi ^ 3) ^ (4 / 3 : ℝ) * (1 / 6 : ℝ) *
            (1 / (2 * (m : ℝ) + 19) ^ 3 - 1 / (2 * (m : ℝ) + 21) ^ 3) :=
          Finset.sum_le_sum hterm
      _ = (560 / Real.pi ^ 3) ^ (4 / 3 : ℝ) * (1 / 6 : ℝ) *
            ∑ m ∈ Finset.range N,
              (1 / (2 * (m : ℝ) + 19) ^ 3 - 1 / (2 * (m : ℝ) + 21) ^ 3) := by
          rw [Finset.mul_sum]
      _ = (560 / Real.pi ^ 3) ^ (4 / 3 : ℝ) * (1 / 6 : ℝ) *
            (1 / (19 : ℝ) ^ 3 - 1 / (2 * (N : ℝ) + 19) ^ 3) := by
          congr 1
          have htel := Finset.sum_range_sub' (fun m : ℕ => (1 : ℝ) / (2 * (m : ℝ) + 19) ^ 3) N
          have heq : (fun m : ℕ => (1 : ℝ) / (2 * (m : ℝ) + 19) ^ 3 -
              1 / (2 * ((m + 1 : ℕ) : ℝ) + 19) ^ 3) =
            (fun m : ℕ => (1 : ℝ) / (2 * (m : ℝ) + 19) ^ 3 -
              1 / (2 * (m : ℝ) + 21) ^ 3) := by
            funext m; push_cast; ring
          rw [heq] at htel
          simpa using htel
      _ ≤ (560 / Real.pi ^ 3) ^ (4 / 3 : ℝ) * (1 / 6 : ℝ) * (1 / (19 : ℝ) ^ 3) := by
          have hC : 0 ≤ (560 / Real.pi ^ 3) ^ (4 / 3 : ℝ) * (1 / 6 : ℝ) := by positivity
          have hnn : 0 ≤ (1 : ℝ) / (2 * (N : ℝ) + 19) ^ 3 := by positivity
          nlinarith
      _ ≤ 1 / 500 := by
          have hpi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
          have hle1 : (560 / Real.pi ^ 3) ^ (4 / 3 : ℝ) * (1 / 6 : ℝ) * (1 / (19 : ℝ) ^ 3) ≤
              (560 / (3.141592 : ℝ) ^ 3) ^ (4 / 3 : ℝ) * (1 / 6 : ℝ) * (1 / (19 : ℝ) ^ 3) := by
            gcongr
          refine le_trans hle1 ?_
          have h3 : ((560 / (3.141592 : ℝ) ^ 3) ^ (4 / 3 : ℝ) * (1 / 6 : ℝ) *
              (1 / (19 : ℝ) ^ 3)) ^ (3 : ℕ) ≤ (1 / 500 : ℝ) ^ (3 : ℕ) := by
            rw [mul_pow, mul_pow,
              ← Real.rpow_natCast ((560 / (3.141592 : ℝ) ^ 3) ^ (4 / 3 : ℝ)) 3,
              ← Real.rpow_mul (by norm_num)]
            norm_num
          exact le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by norm_num) h3
  linarith

private lemma tsum_pHat_rpow_cube_le :
    (∑' r : ℕ, pHat (r + 1) ^ (4 / 3 : ℝ)) ^ 3 ≤ 14 := by
  have htsum : ∑' r : ℕ, pHat (r + 1) ^ (4 / 3 : ℝ) ≤ 24093 / 10000 := by
    rw [← summable_pHat_rpow.sum_add_tsum_nat_add 20]
    have h1 := sum_pHat_head_le
    have h2 : ∑' k : ℕ, pHat (k + 20 + 1) ^ (4 / 3 : ℝ) ≤ 207 / 10000 + 1 / 500 := by
      simpa [add_assoc] using tsum_pHat_tail_le
    linarith
  have hnn : 0 ≤ ∑' r : ℕ, pHat (r + 1) ^ (4 / 3 : ℝ) :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _)
  calc (∑' r : ℕ, pHat (r + 1) ^ (4 / 3 : ℝ)) ^ 3
      ≤ (24093 / 10000 : ℝ) ^ 3 := pow_le_pow_left₀ hnn htsum 3
    _ ≤ 14 := by norm_num

/- ## Main Fourier-analytic lower bound for unit-interval densities -/

private lemma convolution_support_subset {f : ℝ → ℝ}
    (hsupp : Function.support f ⊆ Set.Icc (0 : ℝ) 1) :
    Function.support (f ⋆ f) ⊆ Set.Icc (0 : ℝ) 2 := by
  intro z hz
  by_contra hnot
  apply hz
  rw [convolution_lsmul]
  have hzero : ∀ t : ℝ, f t * f (z - t) = 0 := by
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · have hzt : z - t ∉ Set.Icc (0 : ℝ) 1 := by
        intro hzt
        exact hnot ⟨by linarith [ht.1, hzt.1], by linarith [ht.2, hzt.2]⟩
      have hfz : f (z - t) = 0 := by
        by_contra hne
        exact hzt (hsupp hne)
      rw [hfz, mul_zero]
    · have hft : f t = 0 := by
        by_contra hne
        exact ht (hsupp hne)
      rw [hft, zero_mul]
  simp [hzero]

private lemma fourier_coeff_conv {f : ℝ → ℝ} (hfi : Integrable f)
    (hsupp : Function.support f ⊆ Set.Icc (0 : ℝ) 1) (n : ℤ) :
    ∫ z in Set.Ioc (0 : ℝ) 2, ((f ⋆ f) z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)) =
      (∫ x, (f x : ℂ) * @fourier 2 n (x : AddCircle (2 : ℝ))) ^ 2 := by
  have hgsupp := convolution_support_subset hsupp
  have hIoc : ∫ z in Set.Ioc (0 : ℝ) 2, ((f ⋆ f) z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)) =
      ∫ z, ((f ⋆ f) z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    refine integral_congr_ae ?_
    have hne0 : ∀ᵐ z : ℝ ∂volume, z ≠ 0 := by
      rw [ae_iff]; simp
    filter_upwards [hne0] with z hz0
    by_cases hz : z ∈ Set.Ioc (0 : ℝ) 2
    · simp [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz]
      have hnotIcc : z ∉ Set.Icc (0 : ℝ) 2 := by
        intro h; exact hz ⟨lt_of_le_of_ne h.1 hz0.symm, h.2⟩
      have hg0 : (f ⋆ f) z = 0 := by
        by_contra hne
        exact hnotIcc (hgsupp hne)
      simp [hg0]
  rw [hIoc]
  let φ : ℝ → ℂ := fun x => (f x : ℂ) * @fourier 2 n (x : AddCircle (2 : ℝ))
  have hφ_int : Integrable φ := by
    refine Integrable.mono' hfi.norm ?_ ?_
    · have hcont : Continuous (fun x : ℝ => @fourier 2 n (x : AddCircle (2 : ℝ))) := by
        simp_rw [fourier2_coe]; fun_prop
      exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hfi.aestronglyMeasurable).mul
        hcont.aestronglyMeasurable
    · filter_upwards with x
      simp only [φ, norm_mul, Complex.norm_real, fourier2_norm, mul_one, le_refl]
  have hconv_eq : ∀ z : ℝ,
      ((f ⋆ f) z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)) =
        (φ ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] φ) z := by
    intro z
    rw [convolution_lsmul, convolution_def]
    simp only [ContinuousLinearMap.mul_apply', φ]
    have hofReal : ((∫ t : ℝ, f t * f (z - t) : ℝ) : ℂ) = ∫ t : ℝ, ((f t * f (z - t) : ℝ) : ℂ) := by
      simp_rw [← Complex.coe_algebraMap]
      exact (integral_ofReal (𝕜 := ℂ)).symm
    simp only [smul_eq_mul]
    rw [hofReal, ← integral_mul_const]
    congr 1; funext t
    have hsplit : @fourier 2 n (z : AddCircle (2 : ℝ)) =
        @fourier 2 n (t : AddCircle (2 : ℝ)) * @fourier 2 n ((z - t : ℝ) : AddCircle (2 : ℝ)) := by
      have : z = t + (z - t) := by ring
      conv_lhs => rw [this]
      exact fourier2_add n t (z - t)
    rw [hsplit]
    push_cast; ring
  simp_rw [hconv_eq]
  rw [integral_convolution (ContinuousLinearMap.mul ℝ ℂ) hφ_int hφ_int]
  simp only [ContinuousLinearMap.mul_apply', sq, φ]

private lemma bessel_Ioc_two {g : ℝ → ℝ} (hgi : Integrable g)
    (hg_sq : Integrable (fun z => (g z) ^ 2))
    (c : ℤ → ℂ)
    (hc : ∀ n : ℤ, ∫ z in Set.Ioc (0 : ℝ) 2, (g z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)) = c n)
    (F : Finset ℤ) :
    (1 / 2 : ℝ) * ∑ n ∈ F, ‖c n‖ ^ 2 ≤ ∫ z in Set.Ioc (0 : ℝ) 2, (g z) ^ 2 := by
  let S : ℝ → ℂ := fun z => (1 / 2 : ℂ) * ∑ n ∈ F, c n * @fourier 2 (-n) (z : AddCircle (2 : ℝ))
  have hS_cont : Continuous S := by
    simp only [S]
    refine continuous_const.mul (continuous_finsetSum F fun n _ => ?_)
    simp_rw [fourier2_coe]; fun_prop
  have hS2_int : IntegrableOn (fun z => ‖S z‖ ^ 2) (Set.Ioc (0 : ℝ) 2) volume :=
    (hS_cont.norm.pow 2).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hg2_int : IntegrableOn (fun z => (g z) ^ 2) (Set.Ioc (0 : ℝ) 2) volume :=
    hg_sq.integrableOn
  have hcross_int : IntegrableOn (fun z => (g z : ℂ) * starRingEnd ℂ (S z))
      (Set.Ioc (0 : ℝ) 2) volume := by
    refine Integrable.mono' (hg2_int.add hS2_int) ?_ ?_
    · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
        hgi.aestronglyMeasurable.restrict).mul
        (Complex.continuous_conj.comp hS_cont).aestronglyMeasurable
    · filter_upwards with z
      simp only [Pi.add_apply]
      rw [norm_mul, Complex.norm_real, Complex.norm_conj, Real.norm_eq_abs]
      nlinarith [sq_nonneg (|g z| - ‖S z‖), sq_abs (g z)]
  have hcross_re_int : IntegrableOn (fun z => ((g z : ℂ) * starRingEnd ℂ (S z)).re)
      (Set.Ioc (0 : ℝ) 2) volume :=
    Complex.reCLM.integrable_comp hcross_int
  have hexpand : ∀ z : ℝ,
      ‖(g z : ℂ) - S z‖ ^ 2 =
        (g z) ^ 2 - 2 * ((g z : ℂ) * starRingEnd ℂ (S z)).re + ‖S z‖ ^ 2 := by
    intro z
    rw [Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  have hnonneg : 0 ≤ ∫ z in Set.Ioc (0 : ℝ) 2, ‖(g z : ℂ) - S z‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  simp_rw [hexpand] at hnonneg
  have hsplit_int :
      ∫ z in Set.Ioc (0 : ℝ) 2,
          ((g z) ^ 2 - 2 * ((g z : ℂ) * starRingEnd ℂ (S z)).re + ‖S z‖ ^ 2) =
        (∫ z in Set.Ioc (0 : ℝ) 2, (g z) ^ 2) -
        2 * (∫ z in Set.Ioc (0 : ℝ) 2, ((g z : ℂ) * starRingEnd ℂ (S z)).re) +
        (∫ z in Set.Ioc (0 : ℝ) 2, ‖S z‖ ^ 2) := by
    have hadd := integral_add (hg2_int.sub (hcross_re_int.const_mul 2)) hS2_int
    have hsub := integral_sub hg2_int (hcross_re_int.const_mul 2)
    have hmul := integral_const_mul (μ := volume.restrict (Set.Ioc (0 : ℝ) 2))
      (2 : ℝ) (fun z => ((g z : ℂ) * starRingEnd ℂ (S z)).re)
    dsimp only [Pi.add_apply, Pi.sub_apply] at hadd hsub
    rw [hadd, hsub, hmul]
  rw [hsplit_int] at hnonneg
  have hcross_val :
      ∫ z in Set.Ioc (0 : ℝ) 2, ((g z : ℂ) * starRingEnd ℂ (S z)).re =
        (1 / 2 : ℝ) * ∑ n ∈ F, ‖c n‖ ^ 2 := by
    have hre : ∫ z in Set.Ioc (0 : ℝ) 2, ((g z : ℂ) * starRingEnd ℂ (S z)).re =
        (∫ z in Set.Ioc (0 : ℝ) 2, (g z : ℂ) * starRingEnd ℂ (S z)).re :=
      Complex.reCLM.integral_comp_comm hcross_int
    rw [hre]
    have hpt : (fun z : ℝ => (g z : ℂ) * starRingEnd ℂ (S z)) =
        fun z : ℝ => (1 / 2 : ℂ) * ∑ n ∈ F,
          starRingEnd ℂ (c n) * ((g z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ))) := by
      funext z
      simp only [S, map_mul, map_div₀, map_one, map_ofNat, map_sum, ← fourier_neg, neg_neg,
        Finset.mul_sum]
      ring_nf
    rw [hpt, integral_const_mul, integral_finsetSum]
    · have hterm : ∀ n ∈ F,
          ∫ z in Set.Ioc (0 : ℝ) 2,
            starRingEnd ℂ (c n) * ((g z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ))) =
          starRingEnd ℂ (c n) * c n := by
        intro n _
        rw [integral_const_mul, hc n]
      rw [Finset.sum_congr rfl hterm]
      have hdiv : ((1 / 2 : ℂ) * ∑ n ∈ F, starRingEnd ℂ (c n) * c n).re =
          (1 / 2 : ℝ) * (∑ n ∈ F, starRingEnd ℂ (c n) * c n).re := by
        simp [Complex.mul_re]
      rw [hdiv, Complex.re_sum]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
    · intro n _
      have hcont : Continuous (fun z : ℝ => @fourier 2 n (z : AddCircle (2 : ℝ))) := by
        simp_rw [fourier2_coe]; fun_prop
      have hgn : IntegrableOn (fun z : ℝ => (g z : ℂ) * @fourier 2 n (z : AddCircle (2 : ℝ)))
          (Set.Ioc (0 : ℝ) 2) volume := by
        refine Integrable.mono' hgi.norm.integrableOn ?_ ?_
        · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
            hgi.aestronglyMeasurable.restrict).mul hcont.aestronglyMeasurable
        · filter_upwards with z
          simp only [norm_mul, Complex.norm_real, fourier2_norm, mul_one, le_refl]
      exact hgn.const_mul _
  have hS2_val :
      ∫ z in Set.Ioc (0 : ℝ) 2, ‖S z‖ ^ 2 = (1 / 2 : ℝ) * ∑ n ∈ F, ‖c n‖ ^ 2 := by
    have hpt : (fun z : ℝ => ‖S z‖ ^ 2) = fun z : ℝ => (S z * starRingEnd ℂ (S z)).re := by
      funext z; rw [Complex.sq_norm]; simp [Complex.normSq_apply]
    rw [hpt]
    have hSS_int : IntegrableOn (fun z : ℝ => S z * starRingEnd ℂ (S z))
        (Set.Ioc (0 : ℝ) 2) volume :=
      (hS_cont.mul (Complex.continuous_conj.comp hS_cont)).continuousOn.integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self
    have hre2 : ∫ z in Set.Ioc (0 : ℝ) 2, (S z * starRingEnd ℂ (S z)).re =
        (∫ z in Set.Ioc (0 : ℝ) 2, S z * starRingEnd ℂ (S z)).re :=
      Complex.reCLM.integral_comp_comm hSS_int
    rw [hre2]
    have hexp : (fun z : ℝ => S z * starRingEnd ℂ (S z)) =
        fun z : ℝ => (1 / 4 : ℂ) * ∑ n ∈ F, ∑ m ∈ F,
          (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ)) := by
      funext z
      simp only [S, map_mul, map_div₀, map_one, map_ofNat, map_sum]
      calc (1 / 2 : ℂ) * (∑ n ∈ F, c n * @fourier 2 (-n) (z : AddCircle (2 : ℝ))) *
            ((1 / 2 : ℂ) * ∑ m ∈ F, starRingEnd ℂ (c m) *
              starRingEnd ℂ (@fourier 2 (-m) (z : AddCircle (2 : ℝ))))
          = (1 / 4 : ℂ) * ((∑ n ∈ F, c n * @fourier 2 (-n) (z : AddCircle (2 : ℝ))) *
              (∑ m ∈ F, starRingEnd ℂ (c m) *
                starRingEnd ℂ (@fourier 2 (-m) (z : AddCircle (2 : ℝ))))) := by ring
        _ = (1 / 4 : ℂ) * ∑ n ∈ F, ∑ m ∈ F,
              (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ)) := by
            congr 1
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [← fourier2_mul_conj n m z]; ring
    rw [hexp, integral_const_mul, integral_finsetSum]
    · have hinner : ∀ n ∈ F,
          ∫ z in Set.Ioc (0 : ℝ) 2, ∑ m ∈ F,
            (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ)) =
          (c n * starRingEnd ℂ (c n)) * (2 : ℂ) := by
        intro n hn
        rw [integral_finsetSum]
        · have hterm : ∀ m ∈ F,
              ∫ z in Set.Ioc (0 : ℝ) 2,
                (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ)) =
              if m = n then (c n * starRingEnd ℂ (c m)) * (2 : ℂ) else 0 := by
            intro m _
            rw [integral_const_mul, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2),
              intervalIntegral_fourier2 (m - n)]
            by_cases hmn : m = n
            · subst hmn; simp
            · have : m - n ≠ 0 := sub_ne_zero.mpr hmn
              simp [hmn, this]
          rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' F n, if_pos hn]
        · intro m _
          have hcont : Continuous (fun z : ℝ =>
              (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ))) := by
            simp_rw [fourier2_coe]; fun_prop
          exact hcont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      rw [Finset.sum_congr rfl hinner]
      have hdiv : ((1 / 4 : ℂ) * ∑ n ∈ F, c n * starRingEnd ℂ (c n) * 2).re =
          (1 / 2 : ℝ) * (∑ n ∈ F, c n * starRingEnd ℂ (c n)).re := by
        rw [← Finset.sum_mul, show (1 / 4 : ℂ) * ((∑ n ∈ F, c n * starRingEnd ℂ (c n)) * 2) =
            (1 / 2 : ℂ) * ∑ n ∈ F, c n * starRingEnd ℂ (c n) by ring]
        simp [Complex.mul_re]
      rw [hdiv, Complex.re_sum]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
    · intro n _
      have hcont : Continuous (fun z : ℝ => ∑ m ∈ F,
          (c n * starRingEnd ℂ (c m)) * @fourier 2 (m - n) (z : AddCircle (2 : ℝ))) := by
        refine continuous_finsetSum F fun m _ => ?_
        simp_rw [fourier2_coe]; fun_prop
      exact hcont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  linarith

private lemma integral_sq_conv_ge_four_sevenths {f : ℝ → ℝ} (hf : Green35.IsUnitIntervalDensity f)
    (hgi : Integrable (f ⋆ f))
    (hgsq : Integrable (fun z => ((f ⋆ f) z) ^ 2)) :
    (4 / 7 : ℝ) ≤ ∫ z, ((f ⋆ f) z) ^ 2 := by
  obtain ⟨hfi, hf0, hfsupp, hf1⟩ := hf
  let c : ℤ → ℂ := fun n => ∫ x, (f x : ℂ) * @fourier 2 n (x : AddCircle (2 : ℝ))
  have hc0 : c 0 = 1 := by
    simp only [c, fourier2_zero, mul_one]
    have h1 : ∫ x : ℝ, (f x : ℂ) = ((∫ x : ℝ, f x : ℝ) : ℂ) :=
      Complex.ofRealCLM.integral_comp_comm hfi
    rw [h1, hf1, Complex.ofReal_one]
  have hc_neg : ∀ n : ℤ, ‖c (-n)‖ = ‖c n‖ := by
    intro n
    have hconj : c (-n) = starRingEnd ℂ (c n) := by
      simp only [c]
      rw [← integral_conj]
      congr 1; funext x
      rw [map_mul, Complex.conj_ofReal, fourier_neg]
    rw [hconj, Complex.norm_conj]
  -- Step 1: Bessel inequality for c n ^ 2 via f ⋆ f
  have hg_Ioc : ∫ z in Set.Ioc (0 : ℝ) 2, ((f ⋆ f) z) ^ 2 = ∫ z, ((f ⋆ f) z) ^ 2 := by
    have hgsupp := convolution_support_subset hfsupp
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    refine integral_congr_ae ?_
    have hne0 : ∀ᵐ z : ℝ ∂volume, z ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hne0] with z hz0
    by_cases hz : z ∈ Set.Ioc (0 : ℝ) 2
    · simp [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz]
      have hnotIcc : z ∉ Set.Icc (0 : ℝ) 2 := fun h => hz ⟨lt_of_le_of_ne h.1 hz0.symm, h.2⟩
      have hg0 : (f ⋆ f) z = 0 := by by_contra hne; exact hnotIcc (hgsupp hne)
      simp [hg0]
  have hbessel_partial : ∀ N : ℕ,
      ∑ r ∈ Finset.range N, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4 ≤ (∫ z, ((f ⋆ f) z) ^ 2) - 1 / 2 := by
    intro N
    let F : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
    have hb := bessel_Ioc_two hgi hgsq (fun n => c n ^ 2) (fourier_coeff_conv hfi hfsupp) F
    rw [hg_Ioc] at hb
    have hsum_F : ∑ n ∈ F, ‖c n ^ 2‖ ^ 2 = 1 + 2 * ∑ r ∈ Finset.range N, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4 := by
      have hF_eq : F = insert (0 : ℤ)
          ((Finset.range N).image (fun r : ℕ => ((r + 1 : ℕ) : ℤ)) ∪
           (Finset.range N).image (fun r : ℕ => -((r + 1 : ℕ) : ℤ))) := by
        ext n
        simp only [F, Finset.mem_Icc, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
          Finset.mem_range]
        constructor
        · intro ⟨h1, h2⟩
          by_cases hn0 : n = 0
          · exact Or.inl hn0
          · right
            by_cases hpos : 0 < n
            · left; exact ⟨(n - 1).toNat, by omega, by omega⟩
            · right; exact ⟨(-n - 1).toNat, by omega, by omega⟩
        · rintro (rfl | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) <;> omega
      rw [hF_eq, Finset.sum_insert (by
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range]
        rintro (⟨r, _, hr⟩ | ⟨r, _, hr⟩) <;> omega)]
      have hdisj : Disjoint ((Finset.range N).image (fun r : ℕ => ((r + 1 : ℕ) : ℤ)))
          ((Finset.range N).image (fun r : ℕ => -((r + 1 : ℕ) : ℤ))) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [Finset.mem_image] at hx1 hx2
        obtain ⟨a, _, rfl⟩ := hx1
        obtain ⟨b, _, hb⟩ := hx2
        omega
      rw [Finset.sum_union hdisj,
        Finset.sum_image (by intro a _ b _ h; dsimp at h; omega),
        Finset.sum_image (by intro a _ b _ h; dsimp at h; omega)]
      simp only [hc0, one_pow, norm_one, norm_pow]
      have hpow4 : ∀ z : ℂ, (‖z‖ ^ 2) ^ 2 = ‖z‖ ^ 4 := fun z => by ring
      simp_rw [hpow4, hc_neg]
      ring
    rw [hsum_F] at hb
    have hsimp : (1 / 2 : ℝ) * (1 + 2 * ∑ r ∈ Finset.range N, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4) =
        1 / 2 + ∑ r ∈ Finset.range N, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4 := by ring
    linarith
  have hc_summable : Summable (fun r : ℕ => ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4) :=
    summable_of_sum_range_le (fun _ => by positivity) hbessel_partial
  have hc_tsum_le : ∑' r : ℕ, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4 ≤ (∫ z, ((f ⋆ f) z) ^ 2) - 1 / 2 :=
    hc_summable.tsum_le_of_sum_range_le hbessel_partial
  -- Step 2: Pair f with the Fourier series of U
  have hpair : (1 : ℂ) = ∑' n : ℤ, fourierCoeff U n * c n := by
    have hF_int : ∀ n : ℤ,
        Integrable (fun x : ℝ => (f x : ℂ) * (fourierCoeff U n * @fourier 2 n (x : AddCircle (2 : ℝ)))) := by
      intro n
      have hcont : Continuous (fun x : ℝ => fourierCoeff U n * @fourier 2 n (x : AddCircle (2 : ℝ))) := by
        simp_rw [fourier2_coe]; fun_prop
      refine Integrable.mono' (hfi.norm.const_mul ‖fourierCoeff U n‖) ?_ ?_
      · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hfi.aestronglyMeasurable).mul
          hcont.aestronglyMeasurable
      · filter_upwards with x
        rw [norm_mul, norm_mul, Complex.norm_real, fourier2_norm, mul_one, mul_comm]
    have hF_norm_eq : ∀ n : ℤ,
        ∫ x : ℝ, ‖(f x : ℂ) * (fourierCoeff U n * @fourier 2 n (x : AddCircle (2 : ℝ)))‖ =
          ‖fourierCoeff U n‖ := by
      intro n
      have hpt : (fun x : ℝ => ‖(f x : ℂ) * (fourierCoeff U n * @fourier 2 n (x : AddCircle (2 : ℝ)))‖) =
          (fun x : ℝ => ‖fourierCoeff U n‖ * f x) := by
        funext x
        rw [norm_mul, norm_mul, fourier2_norm, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (hf0 x), mul_comm]
      rw [hpt, integral_const_mul, hf1, mul_one]
    have hF_sum : Summable (fun n : ℤ =>
        ∫ x : ℝ, ‖(f x : ℂ) * (fourierCoeff U n * @fourier 2 n (x : AddCircle (2 : ℝ)))‖) := by
      simp_rw [hF_norm_eq]
      exact summable_fourierCoeff_U.norm
    have hhas := hasSum_integral_of_summable_integral_norm hF_int hF_sum
    have htsum_pt : ∀ x : ℝ,
        (∑' n : ℤ, (f x : ℂ) * (fourierCoeff U n * @fourier 2 n (x : AddCircle (2 : ℝ)))) =
          (f x : ℂ) := by
      intro x
      by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
      · have hU := has_pointwise_sum_fourier_series_of_summable summable_fourierCoeff_U
            (x : AddCircle (2 : ℝ))
        rw [U_coe_of_mem_Icc01 hx] at hU
        have hmul := hU.mul_left (f x : ℂ)
        simpa [smul_eq_mul] using hmul.tsum_eq
      · have hfx : f x = 0 := by by_contra hne; exact hx (hfsupp hne)
        simp [hfx]
    simp_rw [htsum_pt] at hhas
    have hint1 : ∫ x : ℝ, (f x : ℂ) = 1 := by
      have h1 : ∫ x : ℝ, (f x : ℂ) = ((∫ x : ℝ, f x : ℝ) : ℂ) :=
        Complex.ofRealCLM.integral_comp_comm hfi
      rw [h1, hf1, Complex.ofReal_one]
    rw [hint1] at hhas
    have hterm_eq : ∀ n : ℤ,
        ∫ x : ℝ, (f x : ℂ) * (fourierCoeff U n * @fourier 2 n (x : AddCircle (2 : ℝ))) =
          fourierCoeff U n * c n := by
      intro n
      have : (fun x : ℝ => (f x : ℂ) * (fourierCoeff U n * @fourier 2 n (x : AddCircle (2 : ℝ)))) =
          (fun x : ℝ => fourierCoeff U n * ((f x : ℂ) * @fourier 2 n (x : AddCircle (2 : ℝ)))) := by
        funext x; ring
      rw [this, integral_const_mul]
    simp_rw [hterm_eq] at hhas
    exact hhas.tsum_eq.symm
  -- Step 3: Triangle inequality and fold ℤ into ℕ
  have hnorm_sum : Summable (fun n : ℤ => ‖fourierCoeff U n * c n‖) := by
    have hcn_le : ∀ n : ℤ, ‖c n‖ ≤ 1 := by
      intro n
      calc ‖c n‖ ≤ ∫ x, ‖(f x : ℂ) * @fourier 2 n (x : AddCircle (2 : ℝ))‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ x, f x := by
            congr 1; funext x
            rw [norm_mul, fourier2_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg (hf0 x)]
        _ = 1 := hf1
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ summable_fourierCoeff_U.norm
    intro n
    rw [norm_mul]
    calc ‖fourierCoeff U n‖ * ‖c n‖ ≤ ‖fourierCoeff U n‖ * 1 := by gcongr; exact hcn_le n
      _ = ‖fourierCoeff U n‖ := mul_one _
  have h1_le_int : (1 : ℝ) ≤ ∑' n : ℤ, ‖fourierCoeff U n‖ * ‖c n‖ := by
    calc (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
      _ = ‖∑' n : ℤ, fourierCoeff U n * c n‖ := by rw [hpair]
      _ ≤ ∑' n : ℤ, ‖fourierCoeff U n * c n‖ := norm_tsum_le_tsum_norm hnorm_sum
      _ = ∑' n : ℤ, ‖fourierCoeff U n‖ * ‖c n‖ := by simp_rw [norm_mul]
  have hfold : ∑' n : ℤ, ‖fourierCoeff U n‖ * ‖c n‖ =
      ∑' r : ℕ, pHat (r + 1) * ‖c ((r + 1 : ℕ) : ℤ)‖ := by
    let g_int : ℤ → ℝ := fun n => ‖fourierCoeff U n‖ * ‖c n‖
    have hs_int : Summable g_int := by simpa [g_int, norm_mul] using hnorm_sum
    have hs_nat : Summable (fun n : ℕ => g_int n) := hs_int.comp_injective Int.ofNat_injective
    have hs_neg : Summable (fun n : ℕ => g_int (-((n : ℤ) + 1))) :=
      hs_int.comp_injective (by intro a b h; dsimp at h; omega)
    change ∑' n : ℤ, g_int n = _
    rw [tsum_of_nat_of_neg_add_one hs_nat hs_neg]
    have hnat_succ : ∑' n : ℕ, g_int n = ∑' r : ℕ, g_int ((r + 1 : ℕ) : ℤ) := by
      rw [hs_nat.tsum_eq_zero_add]
      simp [g_int, fourierCoeff_U_zero]
    rw [hnat_succ]
    have hneg_eq : (fun r : ℕ => g_int (-((r : ℤ) + 1))) =
        (fun r : ℕ => g_int ((r + 1 : ℕ) : ℤ)) := by
      funext r
      have hcast : -((r : ℤ) + 1) = -((r + 1 : ℕ) : ℤ) := by push_cast; ring
      simp only [g_int, hcast, hc_neg]
      rw [norm_fourierCoeff_U (-((r + 1 : ℕ) : ℤ)) (by omega),
        norm_fourierCoeff_U ((r + 1 : ℕ) : ℤ) (by omega), Int.natAbs_neg]
    rw [hneg_eq, ← two_mul, ← tsum_mul_left]
    congr 1; funext r
    simp only [g_int]
    rw [norm_fourierCoeff_U ((r + 1 : ℕ) : ℤ) (by omega)]
    simp only [Int.natAbs_natCast]
    ring
  have h1_le_nat : (1 : ℝ) ≤ ∑' r : ℕ, pHat (r + 1) * ‖c ((r + 1 : ℕ) : ℤ)‖ := by
    linarith
  -- Step 4: Hölder's inequality with exponents (4/3, 4)
  have hconj : Real.HolderConjugate (4 / 3 : ℝ) 4 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h4eq : (fun r : ℕ => ‖c ((r + 1 : ℕ) : ℤ)‖ ^ (4 : ℝ)) =
      fun r : ℕ => ‖c ((r + 1 : ℕ) : ℤ)‖ ^ (4 : ℕ) := by
    funext r
    exact Real.rpow_natCast _ 4
  have hc_summable_rpow : Summable (fun r : ℕ => ‖c ((r + 1 : ℕ) : ℤ)‖ ^ (4 : ℝ)) := by
    rw [h4eq]; exact hc_summable
  have hholder := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hconj
    (fun r => abs_nonneg _) (fun r => norm_nonneg _) summable_pHat_rpow hc_summable_rpow
  have h1_le_prod : (1 : ℝ) ≤
      (∑' r : ℕ, pHat (r + 1) ^ (4 / 3 : ℝ)) ^ (1 / (4 / 3 : ℝ)) *
      (∑' r : ℕ, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ (4 : ℝ)) ^ (1 / (4 : ℝ)) :=
    h1_le_nat.trans hholder
  have hS_nn : 0 ≤ ∑' r : ℕ, pHat (r + 1) ^ (4 / 3 : ℝ) :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _)
  have hC_nn : 0 ≤ ∑' r : ℕ, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ (4 : ℝ) :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hpow4 : (1 : ℝ) ≤
      (∑' r : ℕ, pHat (r + 1) ^ (4 / 3 : ℝ)) ^ 3 * (∑' r : ℕ, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4) := by
    have h4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) h1_le_prod 4
    rw [one_pow, mul_pow,
      ← Real.rpow_natCast (_ ^ (1 / (4 / 3 : ℝ))) 4, ← Real.rpow_mul hS_nn,
      ← Real.rpow_natCast (_ ^ (1 / (4 : ℝ))) 4, ← Real.rpow_mul hC_nn] at h4
    have e1 : 1 / (4 / 3 : ℝ) * (4 : ℕ) = ((3 : ℕ) : ℝ) := by norm_num
    have e2 : 1 / (4 : ℝ) * (4 : ℕ) = 1 := by norm_num
    rw [e1, e2, Real.rpow_natCast, Real.rpow_one, h4eq] at h4
    exact h4
  have hS3 : (∑' r : ℕ, pHat (r + 1) ^ (4 / 3 : ℝ)) ^ 3 ≤ 14 := tsum_pHat_rpow_cube_le
  have hC_nn4 : 0 ≤ ∑' r : ℕ, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4 := tsum_nonneg (fun _ => by positivity)
  have h1_le_14 : (1 : ℝ) ≤ 14 * ((∫ z, ((f ⋆ f) z) ^ 2) - 1 / 2) := by
    calc (1 : ℝ) ≤ (∑' r : ℕ, pHat (r + 1) ^ (4 / 3 : ℝ)) ^ 3 *
            (∑' r : ℕ, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4) := hpow4
      _ ≤ 14 * (∑' r : ℕ, ‖c ((r + 1 : ℕ) : ℤ)‖ ^ 4) :=
          mul_le_mul_of_nonneg_right hS3 hC_nn4
      _ ≤ 14 * ((∫ z, ((f ⋆ f) z) ^ 2) - 1 / 2) :=
          mul_le_mul_of_nonneg_left hc_tsum_le (by norm_num)
  linarith

end OMA_Green35_c2

open scoped Convolution ENNReal in
theorem OMA.solution : type_of% @Green35.variants.c_2_lower := by
  unfold Green35.c
  apply le_sInf
  rintro r ⟨f, hf, rfl⟩
  by_cases htop : MeasureTheory.eLpNorm (f ⋆ f) 2 MeasureTheory.volume = ⊤
  · rw [htop]; exact le_top
  · have hgi : MeasureTheory.Integrable (f ⋆ f) :=
      hf.1.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf.1
    have h2 : MeasureTheory.eLpNorm (f ⋆ f) 2 MeasureTheory.volume ^ 2 =
        ∫⁻ z, ‖(f ⋆ f) z‖ₑ ^ (2 : ℝ) := by
      rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      have ht : (2 : ℝ≥0∞).toReal = 2 := by norm_num
      rw [ht, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    have hfin : ∫⁻ z, ‖(f ⋆ f) z‖ₑ ^ (2 : ℝ) ≠ ⊤ := by
      rw [← h2]
      exact ENNReal.pow_ne_top htop
    have hgsq_eq : ∀ z, ‖(f ⋆ f) z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (((f ⋆ f) z) ^ 2) := by
      intro z
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
        ← enorm_pow, Real.enorm_eq_ofReal (sq_nonneg _)]
    have hgsq : MeasureTheory.Integrable (fun z => ((f ⋆ f) z) ^ 2) := by
      refine ⟨hgi.aestronglyMeasurable.pow 2, ?_⟩
      rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
      have hconv : (fun z => ‖((f ⋆ f) z) ^ 2‖ₑ) = fun z => ‖(f ⋆ f) z‖ₑ ^ (2 : ℝ) := by
        funext z
        rw [hgsq_eq, Real.enorm_eq_ofReal (sq_nonneg _)]
      rw [hconv]
      exact lt_top_iff_ne_top.mpr hfin
    have hge := OMA_Green35_c2.integral_sq_conv_ge_four_sevenths hf hgi hgsq
    have hsq_le : ENNReal.ofReal (Real.sqrt (4 / 7)) ^ 2 ≤
        MeasureTheory.eLpNorm (f ⋆ f) 2 MeasureTheory.volume ^ 2 := by
      rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num), h2]
      simp_rw [hgsq_eq]
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgsq
        (Filter.Eventually.of_forall (fun z => sq_nonneg _))]
      exact ENNReal.ofReal_le_ofReal hge
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast] at hsq_le
    exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < (2 : ℕ))).mp hsq_le
