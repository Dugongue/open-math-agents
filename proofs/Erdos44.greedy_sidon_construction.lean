import FormalConjectures.ErdosProblems.«44»

-- Problem: Erdős Problem 44: Extending Sidon Sets — greedy sidon construction
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/44.lean:138 (declaration Erdos44.greedy_sidon_construction)
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- This formalises the classical greedy (maximal Sidon set) lower bound |A| >= N^(1/3), see Section 1 of
-- arXiv:2103.15850 (folklore, going back to Erdos). No new mathematical result is claimed.
-- Proof idea: take a Sidon A in {1..N} of maximum size k. Every x in {1..N} outside A is blocked:
-- x = (a+b)/2 with a < b in A, or x = 2b - a with a /= b in A, or x = b + c - a with b < c in A.
-- Hence N <= k + C(k,2) + (k^2 - k) + k C(k,2) = (k^3 + 2k^2 - k)/2 <= k^3.
-- The blocking lemma is adapted from earlier formalisation by the same author
-- (the accepted proof of Erdos340.erdos_340.variants.third, lemma bad_mem).

namespace OMAProof44

/-- midpoints of two distinct elements -/
def M (A : Finset ℕ) : Finset ℕ := (A.powersetCard 2).image (fun s => s.sum id / 2)

/-- values 2b - a with a, b distinct elements -/
def D1 (A : Finset ℕ) : Finset ℕ := A.offDiag.image (fun p => 2 * p.2 - p.1)

/-- values b + c - a with b, c distinct elements -/
def D2 (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A.powersetCard 2).image (fun q => q.2.sum id - q.1)

lemma pair_mem (A : Finset ℕ) (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    ({a, b} : Finset ℕ) ∈ A.powersetCard 2 ∧ ({a, b} : Finset ℕ).sum id = a + b := by
  refine ⟨Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair hab⟩, ?_⟩
  · intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact ha
    · exact hb
  · rw [Finset.sum_pair hab]
    rfl

lemma blocked (A : Finset ℕ) (hA : IsSidon (A : Set ℕ)) (x : ℕ) (hxA : x ∉ A)
    (hx : ¬ IsSidon ((A : Set ℕ) ∪ {x})) : x ∈ M A ∪ D1 A ∪ D2 A := by
  rw [Set.IsSidon.insert hA] at hx
  have hne : ¬ (∀ a ∈ A, ∀ b ∈ A, x + x ≠ a + b ∧ ∀ c ∈ A, x + a ≠ b + c) :=
    fun h => hx (Or.inr h)
  push_neg at hne
  obtain ⟨a, ha, b, hb, h⟩ := hne
  by_cases hxx : x + x = a + b
  · have hab : a ≠ b := by
      intro e
      subst e
      have : x = a := by omega
      exact hxA (this ▸ ha)
    obtain ⟨hp, hs⟩ := pair_mem A a b ha hb hab
    rw [Finset.mem_union, Finset.mem_union]
    left; left
    rw [M, Finset.mem_image]
    exact ⟨{a, b}, hp, by rw [hs]; omega⟩
  · obtain ⟨c, hc, hc'⟩ := h hxx
    by_cases hbc : b = c
    · subst hbc
      have hab : a ≠ b := by
        intro e
        subst e
        have : x = a := by omega
        exact hxA (this ▸ ha)
      rw [Finset.mem_union, Finset.mem_union]
      left; right
      rw [D1, Finset.mem_image]
      exact ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩, by simp only; omega⟩
    · obtain ⟨hp, hs⟩ := pair_mem A b c hb hc hbc
      rw [Finset.mem_union]
      right
      rw [D2, Finset.mem_image]
      exact ⟨(a, {b, c}), Finset.mem_product.mpr ⟨ha, hp⟩, by simp only; rw [hs]; omega⟩

lemma card_cover (A : Finset ℕ) :
    (A ∪ (M A ∪ D1 A ∪ D2 A)).card ≤
      A.card + (A.card.choose 2 + (A.card * A.card - A.card) + A.card * A.card.choose 2) := by
  refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left ?_ _)
  refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ ?_)
  · refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ ?_)
    · exact le_trans Finset.card_image_le (by rw [Finset.card_powersetCard])
    · exact le_trans Finset.card_image_le (by rw [Finset.offDiag_card])
  · exact le_trans Finset.card_image_le (by rw [Finset.card_product, Finset.card_powersetCard])

end OMAProof44

theorem OMA.solution : type_of% @Erdos44.greedy_sidon_construction := by
  intro N hN
  classical
  let F := (Finset.Icc 1 N).powerset.filter (fun A : Finset ℕ => IsSidon (A : Set ℕ))
  have hF : F.Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [F, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.empty_subset _, ?_⟩
    intro i hi
    simp at hi
  obtain ⟨A, hAF, hmax⟩ := F.exists_max_image Finset.card hF
  simp only [F, Finset.mem_filter, Finset.mem_powerset] at hAF
  obtain ⟨hsub, hA⟩ := hAF
  refine ⟨A, hsub, hA, ?_⟩
  have hcov : Finset.Icc 1 N ⊆ A ∪ (OMAProof44.M A ∪ OMAProof44.D1 A ∪ OMAProof44.D2 A) := by
    intro x hx
    by_cases hxA : x ∈ A
    · exact Finset.mem_union_left _ hxA
    · apply Finset.mem_union_right
      apply OMAProof44.blocked A hA x hxA
      intro hs
      have hmem : insert x A ∈ F := by
        simp only [F, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨Finset.insert_subset hx hsub, ?_⟩
        rw [Finset.coe_insert, ← Set.union_singleton]
        exact hs
      have h1 := hmax _ hmem
      have h2 := Finset.card_lt_card (Finset.ssubset_insert hxA)
      omega
  have h1 := Finset.card_le_card hcov
  rw [Nat.card_Icc] at h1
  have h2 := le_trans h1 (OMAProof44.card_cover A)
  have hc : A.card.choose 2 * 2 ≤ A.card * (A.card - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.div_mul_le_self _ _
  rcases Nat.eq_zero_or_pos A.card with h0 | hpos
  · rw [h0] at h2
    simp at h2
    omega
  · obtain ⟨j, hj⟩ : ∃ j, A.card = j + 1 := ⟨A.card - 1, by omega⟩
    rw [hj] at h2 hc ⊢
    have e1 : (j + 1) * (j + 1) - (j + 1) = (j + 1) * j := by
      rw [Nat.mul_succ]
      omega
    have e2 : j + 1 - 1 = j := by omega
    rw [e1] at h2
    rw [e2] at hc
    have hN1 : N + 1 - 1 = N := by omega
    rw [hN1] at h2
    generalize (j + 1).choose 2 = C at h2 hc
    have h3 : (j + 2) * (C * 2) ≤ (j + 2) * ((j + 1) * j) := Nat.mul_le_mul_left _ hc
    nlinarith [h3, h2, Nat.zero_le (j ^ 3 + j ^ 2)]
