import FormalConjectures.ErdosProblems.«340»

-- Problem: Erdős Problem 340 — variant third (the greedy Sidon sequence grows like N^(1/3) at least)
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/340.lean (declaration Erdos340.erdos_340.variants.third)
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- This formalises the classical greedy upper bound for the Mian-Chowla sequence (folklore; Erdos regarded the N^(1/3) bound as trivial). No new mathematical result is claimed.
-- Proof idea: if S is the greedy Sidon set after n steps and g its last element, every x in [1, g') with g' the
-- next element lies in S or is blocked, i.e. x = (a+b)/2 or x = b+c-a with a, b, c in S. Hence
-- g' - 1 <= |S| + |S|^2 + |S|^3, so the n-th term is at most 4 (n+1)^3, which gives the N^(1/3) lower bound.

open Filter Finset

namespace OMAProof340

abbrev S (n : ℕ) : Finset ℕ := (Finset.greedySidon.aux n).1.1

abbrev g (n : ℕ) : ℕ := (Finset.greedySidon.aux n).2

lemma S_sidon (n : ℕ) : IsSidon (S n : Set ℕ) := (Finset.greedySidon.aux n).1.2

lemma S_zero : S 0 = {1} := rfl

lemma g_zero : g 0 = 1 := rfl

lemma S_succ (n : ℕ) : S (n + 1) = S n ∪ {g (n + 1)} := rfl

lemma g_succ (n : ℕ) : g (n + 1) = (Finset.greedySidon.go (S n) (S_sidon n)
    (if h : (S n).Nonempty then (S n).max' h + 1 else g n)).1 := rfl

lemma g_mem (n : ℕ) : g n ∈ S n := by
  cases n with
  | zero => simp [S_zero, g_zero]
  | succ n => rw [S_succ]; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

lemma S_nonempty (n : ℕ) : (S n).Nonempty := ⟨g n, g_mem n⟩

lemma g_succ' (n : ℕ) : g (n + 1) =
    (Finset.greedySidon.go (S n) (S_sidon n) ((S n).max' (S_nonempty n) + 1)).1 := by
  rw [g_succ, dif_pos (S_nonempty n)]

lemma go_min (A : Finset ℕ) (hA : IsSidon (A : Set ℕ)) (m : ℕ) (h : A.Nonempty) (x : ℕ)
    (hx : x < (Finset.greedySidon.go A hA m).1) :
    ¬ (x ≥ m ∧ x ∉ A ∧ IsSidon (↑(A ∪ {x}) : Set ℕ)) := by
  unfold Finset.greedySidon.go at hx
  rw [dif_pos h] at hx
  exact Nat.find_min _ hx

lemma g_succ_ge (n : ℕ) : (S n).max' (S_nonempty n) + 1 ≤ g (n + 1) := by
  rw [g_succ']
  exact (Finset.greedySidon.go (S n) (S_sidon n) ((S n).max' (S_nonempty n) + 1)).2.1

lemma g_lt (n : ℕ) : g n < g (n + 1) := by
  have h1 := g_succ_ge n
  have h2 := (S n).le_max' (g n) (g_mem n)
  omega

lemma le_g (n : ℕ) : ∀ y ∈ S n, y ≤ g n := by
  induction n with
  | zero => intro y hy; rw [S_zero, Finset.mem_singleton] at hy; rw [hy, g_zero]
  | succ n ih =>
    intro y hy
    rw [S_succ, Finset.mem_union, Finset.mem_singleton] at hy
    rcases hy with hy | hy
    · exact le_of_lt (lt_of_le_of_lt (ih y hy) (g_lt n))
    · exact le_of_eq hy

lemma max_eq (n : ℕ) : (S n).max' (S_nonempty n) = g n :=
  le_antisymm ((S n).max'_le _ _ (le_g n)) ((S n).le_max' _ (g_mem n))

lemma between (n x : ℕ) (h1 : g n < x) (h2 : x < g (n + 1)) :
    x ∉ S n ∧ ¬ IsSidon (↑(S n ∪ {x}) : Set ℕ) := by
  have hx : x ∉ S n := fun hm => absurd (le_g n x hm) (by omega)
  refine ⟨hx, fun hs => ?_⟩
  rw [g_succ'] at h2
  refine go_min (S n) (S_sidon n) _ (S_nonempty n) x h2 ⟨?_, hx, hs⟩
  rw [max_eq]
  omega

lemma mono (n x : ℕ) (hb : ¬ IsSidon (↑(S n ∪ {x}) : Set ℕ)) :
    x ∈ S (n + 1) ∨ ¬ IsSidon (↑(S (n + 1) ∪ {x}) : Set ℕ) := by
  by_cases hx : x ∈ S (n + 1)
  · exact Or.inl hx
  · refine Or.inr fun hs => hb (Set.IsSidon.subset hs ?_)
    apply Finset.coe_subset.mpr
    apply Finset.union_subset_union _ (le_refl _)
    rw [S_succ]
    exact Finset.subset_union_left

lemma cover (n : ℕ) : ∀ x, 1 ≤ x → x ≤ g n → x ∈ S n ∨ ¬ IsSidon (↑(S n ∪ {x}) : Set ℕ) := by
  induction n with
  | zero =>
    intro x h1 h2
    left
    rw [g_zero] at h2
    rw [S_zero, Finset.mem_singleton]
    omega
  | succ n ih =>
    intro x h1 h2
    rcases lt_trichotomy x (g (n + 1)) with hlt | heq | hgt
    · by_cases hle : x ≤ g n
      · rcases ih x h1 hle with hm | hb
        · left; rw [S_succ]; exact Finset.mem_union_left _ hm
        · exact mono n x hb
      · exact mono n x (between n x (by omega) hlt).2
    · left; rw [heq]; exact g_mem _
    · omega

lemma cover' (n x : ℕ) (h1 : 1 ≤ x) (h2 : x < g (n + 1)) :
    x ∈ S n ∨ ¬ IsSidon (↑(S n ∪ {x}) : Set ℕ) := by
  by_cases hle : x ≤ g n
  · exact cover n x h1 hle
  · exact Or.inr (between n x (by omega) h2).2

/-- the values blocked by a finite set -/
def T (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A).image (fun p => (p.1 + p.2) / 2) ∪
    ((A ×ˢ A) ×ˢ A).image (fun q => q.1.2 + q.2 - q.1.1)

lemma card_T (A : Finset ℕ) : (T A).card ≤ A.card * A.card + A.card * A.card * A.card := by
  unfold T
  refine le_trans (Finset.card_union_le _ _) (add_le_add ?_ ?_)
  · exact le_trans Finset.card_image_le (by rw [Finset.card_product])
  · exact le_trans Finset.card_image_le (by rw [Finset.card_product, Finset.card_product])

lemma bad_mem (A : Finset ℕ) (hA : IsSidon (A : Set ℕ)) (x : ℕ)
    (hx : ¬ IsSidon (↑(A ∪ {x}) : Set ℕ)) : x ∈ A ∨ x ∈ T A := by
  rw [Finset.coe_union, Finset.coe_singleton, Set.IsSidon.insert hA] at hx
  by_cases hxA : x ∈ A
  · exact Or.inl hxA
  right
  have hne : ¬ (∀ a ∈ A, ∀ b ∈ A, x + x ≠ a + b ∧ ∀ c ∈ A, x + a ≠ b + c) :=
    fun h => hx (Or.inr fun a ha b hb => h a ha b hb)
  push_neg at hne
  obtain ⟨a, ha, b, hb, h⟩ := hne
  unfold T
  rw [Finset.mem_union]
  by_cases hxx : x + x = a + b
  · left
    rw [Finset.mem_image]
    exact ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, by simp only; omega⟩
  · right
    obtain ⟨c, hc, hc'⟩ := h hxx
    rw [Finset.mem_image]
    exact ⟨((a, b), c), Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hc⟩,
      by simp only; omega⟩

lemma card_S (n : ℕ) : (S n).card ≤ n + 1 := by
  induction n with
  | zero => rw [S_zero, Finset.card_singleton]
  | succ n ih =>
    rw [S_succ]
    refine le_trans (Finset.card_union_le _ _) ?_
    rw [Finset.card_singleton]
    omega

lemma g_succ_bound (n : ℕ) :
    g (n + 1) ≤ 1 + (S n).card + ((S n).card * (S n).card + (S n).card * (S n).card * (S n).card) := by
  have hsub : Finset.Ico 1 (g (n + 1)) ⊆ S n ∪ T (S n) := by
    intro x hx
    rw [Finset.mem_Ico] at hx
    rw [Finset.mem_union]
    rcases cover' n x hx.1 hx.2 with hm | hb
    · exact Or.inl hm
    · exact bad_mem (S n) (S_sidon n) x hb
  have h1 := Finset.card_le_card hsub
  rw [Nat.card_Ico] at h1
  have h2 := le_trans h1 (Finset.card_union_le _ _)
  have h3 := card_T (S n)
  omega

lemma g_bound (n : ℕ) : g n ≤ 4 * (n + 1) ^ 3 := by
  cases n with
  | zero => rw [g_zero]; norm_num
  | succ n =>
    have h := g_succ_bound n
    have hk := card_S n
    have hk2 : (S n).card * (S n).card ≤ (n + 1) * (n + 1) := Nat.mul_le_mul hk hk
    have hk3 : (S n).card * (S n).card * (S n).card ≤ (n + 1) * (n + 1) * (n + 1) :=
      Nat.mul_le_mul hk2 hk
    nlinarith

lemma g_strictMono : StrictMono g := strictMono_nat_of_lt_succ g_lt

lemma count (N t : ℕ) (ht : 4 * t ^ 3 ≤ N) :
    t ≤ (Set.range Finset.greedySidon ∩ Set.Icc 1 N).ncard := by
  cases t with
  | zero => exact Nat.zero_le _
  | succ m =>
    have hsub : (((Finset.range (m + 1)).image g : Finset ℕ) : Set ℕ) ⊆
        Set.range Finset.greedySidon ∩ Set.Icc 1 N := by
      intro y hy
      rw [Finset.coe_image, Set.mem_image] at hy
      obtain ⟨i, hi, rfl⟩ := hy
      rw [Finset.coe_range, Set.mem_Iio] at hi
      refine ⟨⟨i, rfl⟩, ?_, ?_⟩
      · have := g_strictMono.monotone (Nat.zero_le i)
        rw [g_zero] at this
        exact this
      · have h1 := g_bound i
        have h2 : (i + 1) ^ 3 ≤ (m + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        omega
    have hfin : (Set.range Finset.greedySidon ∩ Set.Icc 1 N).Finite :=
      (Set.finite_Icc 1 N).subset Set.inter_subset_right
    calc m + 1 = ((Finset.range (m + 1)).image g).card := by
          rw [Finset.card_image_of_injective _ g_strictMono.injective, Finset.card_range]
      _ = ((((Finset.range (m + 1)).image g : Finset ℕ) : Set ℕ)).ncard :=
          (Set.ncard_coe_finset _).symm
      _ ≤ _ := Set.ncard_le_ncard hsub hfin

end OMAProof340

theorem OMA.solution : type_of% @Erdos340.erdos_340.variants.third := by
  intro ε hε
  refine Asymptotics.IsBigO.of_bound 4 ?_
  filter_upwards [eventually_ge_atTop 64] with N hN
  have hx0 : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have hx3 : ((N : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  set x : ℝ := (N : ℝ) ^ ((1 : ℝ) / 3) with hxdef
  have hN' : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hx4 : 4 ≤ x := by
    by_contra hlt
    push_neg at hlt
    nlinarith [mul_nonneg hx0 hx0]
  have ht1 : ((⌊x / 2⌋₊ : ℕ) : ℝ) ≤ x / 2 := Nat.floor_le (by positivity)
  have ht2 : x / 2 - 1 < ((⌊x / 2⌋₊ : ℕ) : ℝ) := Nat.sub_one_lt_floor _
  have htN : 4 * (⌊x / 2⌋₊) ^ 3 ≤ N := by
    have h0 : (0 : ℝ) ≤ ((⌊x / 2⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    have hc : (((⌊x / 2⌋₊ : ℕ) : ℝ)) ^ 3 ≤ (x / 2) ^ 3 := by
      have := mul_le_mul ht1 ht1 h0 (by positivity)
      have := mul_le_mul this ht1 h0 (by positivity)
      nlinarith
    have : (4 * (((⌊x / 2⌋₊ : ℕ) : ℝ)) ^ 3 : ℝ) ≤ N := by nlinarith
    exact_mod_cast this
  have hc := OMAProof340.count N _ htN
  have hcR : ((⌊x / 2⌋₊ : ℕ) : ℝ) ≤
      ((Set.range Finset.greedySidon ∩ Set.Icc 1 N).ncard : ℝ) := by exact_mod_cast hc
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx0, abs_of_nonneg (Nat.cast_nonneg _)]
  linarith
