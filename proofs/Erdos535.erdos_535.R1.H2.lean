import OMAReductions.R_Erdos535_erdos_535_R1

-- Problem: Erdős Problem 535, step H2 of reduction Erdos535.erdos_535.R1 (extraction of a large Ω-layer)
-- Upstream: reductions/Erdos535.erdos_535.R1.lean (hypothesis OMA.R_Erdos535_erdos_535_R1.H2)
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- This is the elementary smooth/rough splitting argument described in the reduction's own docstring; it is a
-- standard pigeonhole argument and no new mathematical result is claimed.
-- Proof idea: split each a in A as a = s(a) r(a), where s(a) is the part of a supported on primes below y and
-- r(a) the part supported on primes at least y. Since a < 2^L every exponent of a is at most L, so the exponent
-- vector of s(a) on {0, ..., y-1} takes at most (L+1)^y values; since y^Ω(r(a)) ≤ r(a) ≤ N < y^(K+1), Ω(r(a)) ≤ K.
-- Classify a by (exponent vector, Ω(r(a))) and take a largest class F. On F the smooth part is a constant s,
-- a ↦ r(a) is injective, and B = r(F) has |A| ≤ (L+1)^y (K+1) |B| and s B ⊆ A.

namespace OMAProof535H2

open Finset ArithmeticFunction

/-- The part of `a` supported on primes below `y`. -/
noncomputable def smooth (y a : ℕ) : ℕ := (a.factorization.filter (fun p => p < y)).prod (· ^ ·)

/-- The part of `a` supported on primes at least `y`. -/
noncomputable def rough (y a : ℕ) : ℕ := (a.factorization.filter (fun p => ¬ p < y)).prod (· ^ ·)

lemma smooth_mul_rough (y a : ℕ) (ha : a ≠ 0) : smooth y a * rough y a = a := by
  unfold smooth rough
  rw [← Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    Finsupp.filter_add_filter_not, Nat.prod_factorization_pow_eq_self ha]

lemma rough_factorization (y a : ℕ) :
    (rough y a).factorization = a.factorization.filter (fun p => ¬ p < y) := by
  unfold rough
  apply Nat.prod_pow_factorization_eq_self
  intro p hp
  rw [Finsupp.support_filter, mem_filter] at hp
  exact Nat.prime_of_mem_primeFactors hp.1

lemma pow_cardFactors_rough_le (y a : ℕ) : y ^ (cardFactors (rough y a)) ≤ rough y a := by
  rw [cardFactors_eq_sum_factorization, rough_factorization]
  set f := a.factorization.filter (fun p => ¬ p < y) with hf
  have key : ∀ p ∈ f.support, y ≤ p := by
    intro p hp
    rw [hf, Finsupp.support_filter, mem_filter] at hp
    omega
  unfold rough
  rw [← hf]
  unfold Finsupp.sum Finsupp.prod
  rw [← prod_pow_eq_pow_sum]
  exact prod_le_prod' (fun p hp => Nat.pow_le_pow_left (key p hp) _)

lemma smooth_congr {y a b : ℕ} (h : ∀ i, i < y → a.factorization i = b.factorization i) :
    smooth y a = smooth y b := by
  unfold smooth
  congr 1
  ext p
  rw [Finsupp.filter_apply, Finsupp.filter_apply]
  split_ifs with hp
  · exact h p hp
  · rfl

lemma factorization_le {a L i : ℕ} (ha : a ≠ 0) (haL : a < 2 ^ L) : a.factorization i ≤ L := by
  by_cases hi : i.Prime
  · have h1 : i ^ a.factorization i ≤ a := Nat.ordProj_le i ha
    have h2 : 2 ^ a.factorization i ≤ i ^ a.factorization i := Nat.pow_le_pow_left hi.two_le _
    have h3 : 2 ^ a.factorization i < 2 ^ L := by omega
    exact ((Nat.pow_lt_pow_iff_right (by norm_num)).mp h3).le
  · rw [Nat.factorization_eq_zero_of_not_prime a hi]
    exact Nat.zero_le _

end OMAProof535H2

open Finset ArithmeticFunction OMAProof535H2 in
theorem OMA.solution : OMA.R_Erdos535_erdos_535_R1.H2 := by
  classical
  intro N y L K hy hL hK A hA
  have hmemA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ N := fun a ha => mem_Icc.mp (hA ha)
  let g : ℕ → (Fin y → ℕ) × ℕ := fun a => (fun i => a.factorization i, cardFactors (rough y a))
  let t : Finset ((Fin y → ℕ) × ℕ) :=
    Fintype.piFinset (fun _ : Fin y => range (L + 1)) ×ˢ range (K + 1)
  have ht : t.card = (L + 1) ^ y * (K + 1) := by
    simp [t, Fintype.card_piFinset]
  have hmaps : ∀ a ∈ A, g a ∈ t := by
    intro a ha
    obtain ⟨h1, h2⟩ := hmemA a ha
    have ha0 : a ≠ 0 := by omega
    rw [mem_product, Fintype.mem_piFinset]
    refine ⟨fun i => mem_range.mpr (Nat.lt_succ_of_le (factorization_le ha0 (by omega))), ?_⟩
    rw [mem_range]
    have hr : rough y a ≤ a := by
      have hd := smooth_mul_rough y a ha0
      have hs0 : smooth y a ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hd; omega
      calc rough y a ≤ smooth y a * rough y a := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hs0)
        _ = a := hd
    have hp := pow_cardFactors_rough_le y a
    have hlt : y ^ (cardFactors (rough y a)) < y ^ (K + 1) := by omega
    exact (Nat.pow_lt_pow_iff_right (by omega)).mp hlt
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · subst hAe
    exact ⟨1, 0, ∅, one_pos, Nat.zero_le _, fun a ha => absurd ha (notMem_empty a),
      by simp, fun b hb => absurd hb (notMem_empty b)⟩
  obtain ⟨a1, ha1⟩ := hAne
  have htne : t.Nonempty := ⟨g a1, hmaps a1 ha1⟩
  obtain ⟨c, hct, hcmax⟩ := exists_max_image t (fun c => (A.filter (fun a => g a = c)).card) htne
  set F := A.filter (fun a => g a = c) with hF
  have hsum : A.card = ∑ b ∈ t, (A.filter (fun a => g a = b)).card :=
    card_eq_sum_card_fiberwise (fun a ha => hmaps a ha)
  have hle : A.card ≤ t.card * F.card := by
    rw [hsum]
    calc ∑ b ∈ t, (A.filter (fun a => g a = b)).card ≤ ∑ _b ∈ t, F.card := sum_le_sum hcmax
      _ = t.card * F.card := by rw [sum_const, smul_eq_mul]
  have hFne : F.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hFe
    rw [hFe, card_empty, mul_zero] at hle
    have : 0 < A.card := card_pos.mpr ⟨a1, ha1⟩
    omega
  obtain ⟨a0, ha0⟩ := hFne
  -- facts about members of F
  have hFmem : ∀ a ∈ F, a ∈ A ∧ g a = c := fun a ha => mem_filter.mp ha
  have hne0 : ∀ a ∈ F, a ≠ 0 := fun a ha => by
    have := (hmemA a (hFmem a ha).1).1; omega
  have hsm : ∀ a ∈ F, smooth y a = smooth y a0 := by
    intro a ha
    apply smooth_congr
    intro i hi
    have e1 := congrArg (fun z => z.1 ⟨i, hi⟩) (hFmem a ha).2
    have e2 := congrArg (fun z => z.1 ⟨i, hi⟩) (hFmem a0 ha0).2
    simp only [g] at e1 e2
    rw [e1, e2]
  have hinj : Set.InjOn (rough y) (F : Set ℕ) := by
    intro a ha b hb hab
    have da := smooth_mul_rough y a (hne0 a ha)
    have db := smooth_mul_rough y b (hne0 b hb)
    rw [← da, ← db, hsm a ha, hsm b hb, hab]
  refine ⟨smooth y a0, c.2, F.image (rough y), ?_, ?_, ?_, ?_, ?_⟩
  · have d := smooth_mul_rough y a0 (hne0 a0 ha0)
    apply Nat.pos_of_ne_zero
    intro h0
    rw [h0, zero_mul] at d
    exact hne0 a0 ha0 d.symm
  · have := (mem_product.mp hct).2
    rw [mem_range] at this
    omega
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    refine ⟨?_, ?_⟩
    · have d := smooth_mul_rough y a (hne0 a ha)
      apply Nat.pos_of_ne_zero
      intro h0
      rw [h0, mul_zero] at d
      exact hne0 a ha d.symm
    · have e := congrArg Prod.snd (hFmem a ha).2
      simpa [g] using e
  · rw [card_image_of_injOn hinj, ← ht]
    exact hle
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    rw [← hsm a ha, smooth_mul_rough y a (hne0 a ha)]
    exact (hFmem a ha).1
