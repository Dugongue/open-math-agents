import OMAStatements.S_oeis_a054656

/-!
# OEIS A054656: primes missing from all partitions of `n` into distinct primes

Outline.  A prime `p ≤ n` appears in a partition of `n` into distinct primes iff `n - p` is a
sum of distinct primes different from `p`.

* Part A (density input).  For every `n ≥ 7` there are two distinct primes in `(n, 2n]`.  For
  `n ≥ 512` this is the central binomial coefficient argument of Mathlib's proof of Bertrand's
  postulate (`Mathlib/NumberTheory/Bertrand.lean`, Apache-2.0), adapted to allow one prime in
  `(n, 2n]`: that prime contributes a factor `≤ 2n`, which is absorbed because there are at most
  `sqrt (2n) - 1` primes `≤ sqrt (2n)`; so Mathlib's `bertrand_main_inequality` still applies.
  For `7 ≤ n < 547` a chain of primes `7, 11, 13, 19, …, 547, 631` with `p_{i+2} ≤ 2 p_i` is used.
* Part B (Richert-style induction).  For every `q` and every `m ≥ 13`, `m` is a sum of distinct
  primes different from `q`.  Invariant: every `m ∈ [13, b)` is a sum of distinct primes `≤ B`
  different from `q`, with `2B + 13 ≤ b`; a new prime `p ≠ q` in `(B, 2B]` extends this to
  `[13, b + p)`.  The base `B = 23`, `b = 59` is a decidable subset-sum check.
* Part C.  `1, 4, 6` are not sums of distinct primes, the remaining `m ≤ 12` are sums of distinct
  primes `≤ 11`, and a parity argument gives the count.
-/

namespace OMA.P054656

open Finset OMA.S_oeis_a054656

/-! ### Part A: two primes in `(n, 2n]` -/

/-- Adapted from Mathlib's `centralBinom_le_of_no_bertrand_prime`: the same bound holds if
`(n, 2n]` contains at most one prime. -/
theorem centralBinom_le_of_one_prime (n : ℕ) (n_large : 2 < n) (q0 : ℕ)
    (h : ∀ p : ℕ, p.Prime → n < p → p ≤ 2 * n → p = q0) :
    Nat.centralBinom n ≤ (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) := by
  have n_pos : 0 < n := by omega
  have n2_pos : 1 ≤ 2 * n := by omega
  let f : ℕ → ℕ := fun x => x ^ n.centralBinom.factorization x
  have hf_le : ∀ x, f x ≤ 2 * n := fun x =>
    Nat.pow_factorization_choose_le (mul_pos two_pos n_pos)
  have hf_np : ∀ x, ¬ x.Prime → f x = 1 := by
    intro x hx
    show x ^ _ = 1
    rw [Nat.factorization_eq_zero_of_not_prime _ hx, pow_zero]
  have hsplit : Nat.centralBinom n
      = (∏ x ∈ range (2 * n / 3 + 1), f x) * ∏ x ∈ Ico (2 * n / 3 + 1) (2 * n + 1), f x := by
    rw [Finset.prod_range_mul_prod_Ico f (by omega)]
    exact n.prod_pow_factorization_centralBinom.symm
  have htail : ∏ x ∈ Ico (2 * n / 3 + 1) (2 * n + 1), f x ≤ 2 * n := by
    have h1 : ∀ x ∈ Ico (2 * n / 3 + 1) (2 * n + 1), x ≠ q0 → f x = 1 := by
      intro x hx hne
      rw [Finset.mem_Ico] at hx
      by_cases hp : x.Prime
      · have hxn : x ≤ n := by
          by_contra hlt
          exact hne (h x hp (by omega) (by omega))
        show x ^ _ = 1
        rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul n_large hxn (by omega),
          pow_zero]
      · exact hf_np x hp
    by_cases hq : q0 ∈ Ico (2 * n / 3 + 1) (2 * n + 1)
    · rw [Finset.prod_eq_single_of_mem q0 hq (fun x hx hne => h1 x hx hne)]
      exact hf_le q0
    · rw [Finset.prod_eq_one (fun x hx => h1 x hx (fun e => hq (e ▸ hx)))]
      exact n2_pos
  let S : Finset ℕ := (range (2 * n / 3 + 1)).filter Nat.Prime
  have hS : ∏ x ∈ S, f x = ∏ x ∈ range (2 * n / 3 + 1), f x := by
    refine Finset.prod_filter_of_ne fun p _ hne => ?_
    by_contra hp
    exact hne (hf_np p hp)
  have hsmall : ∏ x ∈ S.filter (· ≤ Nat.sqrt (2 * n)), f x ≤ (2 * n) ^ (Nat.sqrt (2 * n) - 1) := by
    refine (Finset.prod_le_prod' fun p _ => hf_le p).trans ?_
    rw [Finset.prod_const]
    refine pow_right_mono₀ n2_pos
      ((Finset.card_le_card (t := Finset.Icc 2 (Nat.sqrt (2 * n))) fun x hx => ?_).trans ?_)
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.two_le, h2⟩
    · rw [Nat.card_Icc]; omega
  have hbig : ∏ x ∈ S.filter (fun x => ¬ x ≤ Nat.sqrt (2 * n)), f x ≤ 4 ^ (2 * n / 3) := by
    refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
    refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp <| not_le.1 h2)
    refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
    exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le
  have hsq : 1 ≤ Nat.sqrt (2 * n) := Nat.le_sqrt.2 (by omega)
  obtain ⟨k, hk⟩ : ∃ k, Nat.sqrt (2 * n) = k + 1 := ⟨Nat.sqrt (2 * n) - 1, by omega⟩
  calc Nat.centralBinom n
      = ((∏ x ∈ S.filter (· ≤ Nat.sqrt (2 * n)), f x)
          * ∏ x ∈ S.filter (fun x => ¬ x ≤ Nat.sqrt (2 * n)), f x)
          * ∏ x ∈ Ico (2 * n / 3 + 1) (2 * n + 1), f x := by
        rw [hsplit, ← hS, Finset.prod_filter_mul_prod_filter_not]
    _ ≤ ((2 * n) ^ (Nat.sqrt (2 * n) - 1) * 4 ^ (2 * n / 3)) * (2 * n) :=
        Nat.mul_le_mul (Nat.mul_le_mul hsmall hbig) htail
    _ = (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) := by
        rw [hk, Nat.add_sub_cancel, pow_succ]; ring

/-- The statement that `(n, 2n]` contains two distinct primes. -/
def TwoPrimes (n : ℕ) : Prop :=
  ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≠ r ∧ n < p ∧ p ≤ 2 * n ∧ n < r ∧ r ≤ 2 * n

theorem twoPrimes_large (n : ℕ) (hn : 512 ≤ n) : TwoPrimes n := by
  obtain ⟨p, hp, hnp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  by_contra hno
  have hall : ∀ r : ℕ, r.Prime → n < r → r ≤ 2 * n → r = p := by
    intro r hr h1 h2
    by_contra hne
    exact hno ⟨p, r, hp, hr, fun e => hne e.symm, hnp, hp2, h1, h2⟩
  have h1 : 4 ^ n < n * n.centralBinom := Nat.four_pow_lt_mul_centralBinom n (by omega)
  have h2 := centralBinom_le_of_one_prime n (by omega) p hall
  have h3 := bertrand_main_inequality hn
  have h4 : n * n.centralBinom ≤ 4 ^ n :=
    (Nat.mul_le_mul_left n h2).trans (by rw [← mul_assoc]; exact h3)
  omega

theorem twoPrimes_step {n : ℕ} (a b c : ℕ) (hb : b.Prime) (hc : c.Prime) (hbc : b < c)
    (hca : c ≤ 2 * a) (ha : a ≤ n) (H : b ≤ n → TwoPrimes n) : TwoPrimes n := by
  by_cases hbn : b ≤ n
  · exact H hbn
  · exact ⟨b, c, hb, hc, by omega, by omega, by omega, by omega, by omega⟩

theorem twoPrimes (n : ℕ) (hn : 7 ≤ n) : TwoPrimes n := by
  refine twoPrimes_step 7 11 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
    fun hn => ?_
  refine twoPrimes_step 11 13 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
    fun hn => ?_
  refine twoPrimes_step 13 19 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
    fun hn => ?_
  refine twoPrimes_step 19 23 37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
    fun hn => ?_
  refine twoPrimes_step 23 37 43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
    fun hn => ?_
  refine twoPrimes_step 37 43 73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
    fun hn => ?_
  refine twoPrimes_step 43 73 83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
    fun hn => ?_
  refine twoPrimes_step 73 83 139 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
    fun hn => ?_
  refine twoPrimes_step 83 139 163 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
    fun hn => ?_
  refine twoPrimes_step 139 163 277 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
    fun hn => ?_
  refine twoPrimes_step 163 277 317 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
    fun hn => ?_
  refine twoPrimes_step 277 317 547 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
    fun hn => ?_
  refine twoPrimes_step 317 547 631 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hn
    fun hn => ?_
  exact twoPrimes_large n (by omega)

/-! ### Part B: sums of distinct primes avoiding `q` -/

/-- Subset-sum check: is `m` a sum of a sublist of `L`? -/
def chk : List ℕ → ℕ → Bool
  | [], m => decide (m = 0)
  | p :: L, m => chk L m || (decide (p ≤ m) && chk L (m - p))

theorem chk_sound : ∀ (L : List ℕ) (m : ℕ), L.Nodup → chk L m = true →
    ∃ s : Finset ℕ, (∀ r ∈ s, r ∈ L) ∧ ∑ r ∈ s, r = m := by
  intro L
  induction L with
  | nil =>
    intro m _ h
    refine ⟨∅, by simp, ?_⟩
    simp only [chk, decide_eq_true_eq] at h
    simp [h]
  | cons p L ih =>
    intro m hnd h
    rw [List.nodup_cons] at hnd
    simp only [chk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨hpm, h⟩
    · obtain ⟨s, hs, hsum⟩ := ih m hnd.2 h
      exact ⟨s, fun r hr => List.mem_cons_of_mem _ (hs r hr), hsum⟩
    · obtain ⟨s, hs, hsum⟩ := ih (m - p) hnd.2 h
      have hps : p ∉ s := fun hp => hnd.1 (hs p hp)
      refine ⟨insert p s, ?_, ?_⟩
      · intro r hr
        rcases Finset.mem_insert.1 hr with rfl | hr
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hs r hr)
      · rw [Finset.sum_insert hps, hsum]; omega

/-- `m` is a sum of distinct primes `≤ B` different from `q`. -/
def Rep (q B m : ℕ) : Prop :=
  ∃ s : Finset ℕ, (∀ r ∈ s, r.Prime ∧ r ≠ q ∧ r ≤ B) ∧ ∑ r ∈ s, r = m

set_option maxRecDepth 100000 in
theorem base_check : ∀ q < 24, ∀ m < 59, 13 ≤ m →
    chk ([2, 3, 5, 7, 11, 13, 17, 19, 23].filter (fun r => decide (r ≠ q))) m = true := by
  decide

theorem base_mem : ∀ r ∈ [2, 3, 5, 7, 11, 13, 17, 19, 23], r.Prime ∧ r ≤ 23 := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem rep_base (q m : ℕ) (h1 : 13 ≤ m) (h2 : m < 59) : Rep q 23 m := by
  by_cases hq : q < 24
  · obtain ⟨s, hs, hsum⟩ := chk_sound _ m (List.Nodup.filter _ (by decide))
      (base_check q hq m h2 h1)
    refine ⟨s, fun r hr => ?_, hsum⟩
    have := List.mem_filter.1 (hs r hr)
    exact ⟨(base_mem r this.1).1, by simpa using this.2, (base_mem r this.1).2⟩
  · obtain ⟨s, hs, hsum⟩ := chk_sound _ m (List.Nodup.filter _ (by decide))
      (base_check 0 (by norm_num) m h2 h1)
    refine ⟨s, fun r hr => ?_, hsum⟩
    have := List.mem_filter.1 (hs r hr)
    have hb := base_mem r this.1
    exact ⟨hb.1, by omega, hb.2⟩

theorem rep_step (q B b p : ℕ) (hp : p.Prime) (hpq : p ≠ q) (hBp : B < p) (hpb : p + 13 ≤ b)
    (W : ∀ m, 13 ≤ m → m < b → Rep q B m) : ∀ m, 13 ≤ m → m < b + p → Rep q p m := by
  intro m h1 h2
  by_cases hm : m < b
  · obtain ⟨s, hs, hsum⟩ := W m h1 hm
    exact ⟨s, fun r hr => ⟨(hs r hr).1, (hs r hr).2.1, by have := (hs r hr).2.2; omega⟩, hsum⟩
  · obtain ⟨s, hs, hsum⟩ := W (m - p) (by omega) (by omega)
    have hps : p ∉ s := fun hin => by have := (hs p hin).2.2; omega
    refine ⟨insert p s, ?_, ?_⟩
    · intro r hr
      rcases Finset.mem_insert.1 hr with rfl | hr
      · exact ⟨hp, hpq, le_refl _⟩
      · exact ⟨(hs r hr).1, (hs r hr).2.1, by have := (hs r hr).2.2; omega⟩
    · rw [Finset.sum_insert hps, hsum]; omega

theorem rep_all (q : ℕ) : ∀ k : ℕ, ∃ B b : ℕ, 23 ≤ B ∧ 2 * B + 13 ≤ b ∧ 59 + k ≤ b ∧
    ∀ m, 13 ≤ m → m < b → Rep q B m := by
  intro k
  induction k with
  | zero => exact ⟨23, 59, le_refl _, by norm_num, by norm_num, fun m h1 h2 => rep_base q m h1 h2⟩
  | succ k ih =>
    obtain ⟨B, b, hB, hb, hk, W⟩ := ih
    obtain ⟨p, r, hp, hr, hpr, hBp, hp2, hBr, hr2⟩ := twoPrimes B (by omega)
    by_cases hpq : p = q
    · exact ⟨r, b + r, by omega, by omega, by omega,
        rep_step q B b r hr (fun e => hpr (hpq.trans e.symm)) hBr (by omega) W⟩
    · exact ⟨p, b + p, by omega, by omega, by omega, rep_step q B b p hp hpq hBp (by omega) W⟩

/-- Every `m ≥ 13` is a sum of distinct primes different from `q`. -/
theorem rep_ge (q m : ℕ) (hm : 13 ≤ m) :
    ∃ s : Finset ℕ, (∀ r ∈ s, r.Prime) ∧ q ∉ s ∧ ∑ r ∈ s, r = m := by
  obtain ⟨B, b, _, _, hk, W⟩ := rep_all q m
  obtain ⟨s, hs, hsum⟩ := W m hm (by omega)
  exact ⟨s, fun r hr => (hs r hr).1, fun hq => (hs q hq).2.1 rfl, hsum⟩

/-! ### Part C: the classification -/

theorem small_check : ∀ m < 13, m ≠ 1 → m ≠ 4 → m ≠ 6 → m ≠ 11 → chk [2, 3, 5, 7] m = true := by
  decide

/-- For `p ≥ 11` (and `p ≠ 11` when `m = 11`), every `m ≤ 12` other than `1, 4, 6` is a sum of
distinct primes different from `p`. -/
theorem rep_small (p m : ℕ) (hm : m < 13) (h1 : m ≠ 1) (h4 : m ≠ 4) (h6 : m ≠ 6)
    (hp : 23 ≤ m + p) :
    ∃ s : Finset ℕ, (∀ r ∈ s, r.Prime) ∧ p ∉ s ∧ ∑ r ∈ s, r = m := by
  by_cases h11 : m = 11
  · refine ⟨{11}, ?_, ?_, ?_⟩
    · intro r hr
      rw [Finset.mem_singleton] at hr
      subst hr; norm_num
    · rw [Finset.mem_singleton]; omega
    · rw [Finset.sum_singleton, h11]
  · obtain ⟨s, hs, hsum⟩ := chk_sound _ m (by decide) (small_check m hm h1 h4 h6 h11)
    have hmem : ∀ r ∈ s, r.Prime ∧ r ≤ 7 := by
      intro r hr
      have := hs r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl <;> norm_num
    exact ⟨s, fun r hr => (hmem r hr).1, fun hin => by have := (hmem p hin).2; omega, hsum⟩

/-- `1`, `4`, `6` are not sums of distinct primes. -/
theorem no_rep (t : Finset ℕ) (ht : ∀ r ∈ t, r.Prime) :
    ∑ r ∈ t, r ≠ 1 ∧ ∑ r ∈ t, r ≠ 4 ∧ ∑ r ∈ t, r ≠ 6 := by
  by_cases hbig : 6 < ∑ r ∈ t, r
  · omega
  have hsub : t ∈ ({2, 3, 5} : Finset ℕ).powerset := by
    rw [Finset.mem_powerset]
    intro r hr
    have hle : r ≤ ∑ x ∈ t, x := Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _) hr
    have hpr := ht r hr
    have hr6 : r ≤ 6 := by omega
    interval_cases r <;> first | decide | (exact absurd hpr (by norm_num))
  have key : ∀ u ∈ ({2, 3, 5} : Finset ℕ).powerset,
      ∑ r ∈ u, r ≠ 1 ∧ ∑ r ∈ u, r ≠ 4 ∧ ∑ r ∈ u, r ≠ 6 := by decide
  exact key t hsub

theorem appears_iff (n p : ℕ) (hn : 23 ≤ n) (hp : p.Prime) (hpn : p ≤ n) :
    ¬ Appears n p ↔ (n - p = 1 ∨ n - p = 4 ∨ n - p = 6) := by
  constructor
  · intro hA
    by_contra hne
    apply hA
    have hex : ∃ s : Finset ℕ, (∀ r ∈ s, r.Prime) ∧ p ∉ s ∧ ∑ r ∈ s, r = n - p := by
      by_cases hm : 13 ≤ n - p
      · exact rep_ge p (n - p) hm
      · exact rep_small p (n - p) (by omega) (by omega) (by omega) (by omega) (by omega)
    obtain ⟨s, hs, hps, hsum⟩ := hex
    refine ⟨insert p s, ?_, Finset.mem_insert_self _ _, ?_⟩
    · intro r hr
      rcases Finset.mem_insert.1 hr with rfl | hr
      · exact hp
      · exact hs r hr
    · rw [Finset.sum_insert hps, hsum]; omega
  · rintro h ⟨s, hs, hps, hsum⟩
    have h1 := Finset.sum_erase_add s (fun x => x) hps
    have h2 := no_rep (s.erase p) (fun r hr => hs r (Finset.mem_of_mem_erase hr))
    omega

theorem parity {x y : ℕ} (hx : x.Prime) (hy : y.Prime) (h3x : 3 ≤ x) (h3y : 3 ≤ y) :
    (x + y) % 2 = 0 := by
  rcases hx.eq_two_or_odd with h | h
  · omega
  rcases hy.eq_two_or_odd with h' | h'
  · omega
  omega

theorem main_aux : ∀ n : ℕ, 23 ≤ n →
    a n = if (n - 6).Prime ∧ (n - 4).Prime then 2
      else if (n - 6).Prime ∨ (n - 4).Prime ∨ (n - 1).Prime then 1 else 0 := by
  intro n hn
  have hset : {p : ℕ | p.Prime ∧ p ≤ n ∧ ¬ Appears n p}
      = ((({n - 1, n - 4, n - 6} : Finset ℕ).filter Nat.Prime : Finset ℕ) : Set ℕ) := by
    ext p
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, hpn, hA⟩
      have := (appears_iff n p hn hp hpn).1 hA
      exact ⟨by omega, hp⟩
    · rintro ⟨hmem, hp⟩
      have hpn : p ≤ n := by omega
      exact ⟨hp, hpn, (appears_iff n p hn hp hpn).2 (by omega)⟩
  have hAB : ¬ ((n - 1).Prime ∧ (n - 4).Prime) := by
    rintro ⟨h1, h2⟩
    have := parity h1 h2 (by omega) (by omega)
    omega
  have hAC : ¬ ((n - 1).Prime ∧ (n - 6).Prime) := by
    rintro ⟨h1, h2⟩
    have := parity h1 h2 (by omega) (by omega)
    omega
  have hn1 : n - 1 ∉ ({n - 4, n - 6} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hn2 : n - 4 ∉ ({n - 6} : Finset ℕ) := by
    simp only [Finset.mem_singleton]; omega
  unfold a
  rw [hset, Set.ncard_coe_finset, Finset.card_filter, Finset.sum_insert hn1,
    Finset.sum_insert hn2, Finset.sum_singleton]
  by_cases hA : (n - 1).Prime <;> by_cases hB : (n - 4).Prime <;> by_cases hC : (n - 6).Prime <;>
    simp_all

end OMA.P054656

theorem OMA.solution : type_of% @OMA.S_oeis_a054656.main := OMA.P054656.main_aux
