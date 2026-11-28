import OMAStatements.S_oeis_a052542
import Mathlib

namespace OMA.A052542Proof

open OMA.S_oeis_a052542 Finset

/-- Lists of positive integers with sum `n`, built by first part. -/
def T : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | n + 1 => (range (n + 1)).biUnion (fun p => (T (n - p)).image (List.cons (p + 1)))
decreasing_by omega

theorem mem_T : ∀ n (l : List ℕ), l ∈ T n ↔ (∀ x ∈ l, 0 < x) ∧ l.sum = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l
    cases n with
    | zero =>
      rw [T, mem_singleton]
      constructor
      · rintro rfl; simp
      · rintro ⟨hp, hs⟩
        cases l with
        | nil => rfl
        | cons x l =>
          have := hp x (by simp)
          simp at hs; omega
    | succ n =>
      rw [T, mem_biUnion]
      constructor
      · rintro ⟨p, hp, hl⟩
        rw [mem_image] at hl
        obtain ⟨l', hl', rfl⟩ := hl
        rw [ih (n - p) (by omega)] at hl'
        rw [mem_range] at hp
        refine ⟨?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with h | h
          · omega
          · exact hl'.1 x h
        · simp [hl'.2]; omega
      · rintro ⟨hpos, hs⟩
        cases l with
        | nil => simp at hs
        | cons x l' =>
          have hx := hpos x (by simp)
          simp only [List.sum_cons] at hs
          refine ⟨x - 1, by rw [mem_range]; omega, ?_⟩
          rw [mem_image]
          refine ⟨l', ?_, by congr 1; omega⟩
          rw [ih (n - (x - 1)) (by omega)]
          exact ⟨fun y hy => hpos y (by simp [hy]), by omega⟩

/-- Weight of a list. -/
def w (l : List ℕ) : ℕ := if ∀ x ∈ l, Odd x then 2 ^ l.length else 0

def F (n : ℕ) : ℕ := ∑ l ∈ T n, w l

theorem w_cons (p : ℕ) (l : List ℕ) : w (p :: l) = if Odd p then 2 * w l else 0 := by
  unfold w
  by_cases hp : Odd p
  · by_cases hl : ∀ x ∈ l, Odd x
    · simp [hp, hl, pow_succ, mul_comm]
    · simp [hp, hl]
  · simp [hp]

theorem F_succ (n : ℕ) :
    F (n + 1) = ∑ p ∈ range (n + 1), if Odd (p + 1) then 2 * F (n - p) else 0 := by
  unfold F
  rw [T, sum_biUnion]
  · apply sum_congr rfl
    intro p _
    rw [sum_image (fun x _ y _ h => List.cons_injective h)]
    simp_rw [w_cons]
    split_ifs
    · rw [mul_sum]
    · simp
  · intro p _ q _ hpq
    simp only [Function.onFun]
    rw [disjoint_left]
    intro l hl hl'
    rw [mem_image] at hl hl'
    obtain ⟨a, _, rfl⟩ := hl
    obtain ⟨b, _, hb⟩ := hl'
    have := List.head_eq_of_cons_eq hb
    omega

theorem F_rec (n : ℕ) : F (n + 3) = 2 * F (n + 2) + F (n + 1) := by
  rw [F_succ (n + 2), sum_range_succ', sum_range_succ', F_succ n]
  have h1 : ¬ Odd (0 + 1 + 1) := by decide
  simp only [zero_add, Nat.sub_zero, if_pos odd_one, h1, if_false, add_zero]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro p hp
  rw [mem_range] at hp
  have e : n + 2 - (p + 1 + 1) = n - p := by omega
  rw [e]
  have : Odd (p + 1 + 1 + 1) ↔ Odd (p + 1) := by
    rw [show p + 1 + 1 + 1 = (p + 1) + 2 by ring, Nat.odd_add]; simp
  simp only [this]

theorem F_one : F 1 = 2 := by
  rw [F_succ]; simp [F, T, w]

theorem F_two : F 2 = 4 := by
  rw [F_succ, sum_range_succ, sum_range_succ, F_one]; simp [F, T, w]

theorem a_eq_F : ∀ n, 1 ≤ n → a n = F n
  | 0 => by intro h; omega
  | 1 => by intro _; rw [F_one]; rfl
  | 2 => by intro _; rw [F_two]; rfl
  | n + 3 => by
    intro _
    rw [F_rec, ← a_eq_F (n + 2) (by omega), ← a_eq_F (n + 1) (by omega)]
    rfl

theorem sum_eq (n : ℕ) :
    ∑ c ∈ (univ : Finset (Composition n)).filter (fun c => ∀ p ∈ c.blocks, Odd p), 2 ^ c.length =
      F n := by
  rw [sum_filter]
  have emb : Composition n ↪ List ℕ := ⟨fun c => c.blocks, fun c d h => Composition.ext h⟩
  have hT : univ.map ⟨fun c : Composition n => c.blocks, fun c d h => Composition.ext h⟩ = T n := by
    ext l
    rw [mem_map, mem_T]
    constructor
    · rintro ⟨c, _, rfl⟩
      exact ⟨fun x hx => c.blocks_pos hx, c.blocks_sum⟩
    · rintro ⟨hp, hs⟩
      exact ⟨⟨l, fun hx => hp _ hx, hs⟩, mem_univ _, rfl⟩
  unfold F
  rw [← hT, sum_map]
  rfl

end OMA.A052542Proof

open OMA.A052542Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a052542.main := by
  intro n hn
  rw [sum_eq, a_eq_F n hn]
