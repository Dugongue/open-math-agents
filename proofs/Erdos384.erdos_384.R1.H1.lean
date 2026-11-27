import OMAReductions.R_Erdos384_erdos_384_R1

/-!
# Erdős Problem 384, reduction R1, step H1: Ecklund's first case (k ≥ 4, k² < n)

Upstream path: reductions/Erdos384.erdos_384.R1.lean, hypothesis H1.
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

This formalises the first case of Ecklund's theorem
(E. F. Ecklund Jr., On prime divisors of the binomial coefficient, Pacific J. Math. 29
(1969)); no new result is claimed.

Proof idea. Suppose every prime factor p of C = C(n, k) has 2p > n. Then p² > n, so C is
squarefree; and p divides one of n - i (i < k), which forces p = n - i, so every prime factor
lies in (n - k, n]. These primes are odd and prime to 3. Mapping p to (n - p) / 2 is injective,
and lands in a set of size at most k / 2 (for odd k one value is lost: either by parity, or
because one of n, n - 2, n - 4 is a multiple of 3). Hence C ≤ n^t with 2t ≤ k. On the other
hand n^k ≤ C · k^k, since (n - i) k ≥ n (k - i) termwise. Together n^k ≤ n^(k/2) k^k,
i.e. n ≤ k², a contradiction.
-/

open Finset

namespace OMA.E384H1

/-- `n^k ≤ C(n,k) * k^k` for `k ≤ n`. -/
theorem pow_le_choose_mul (n k : ℕ) (hkn : k ≤ n) : n ^ k ≤ n.choose k * k ^ k := by
  have hd := Nat.descFactorial_eq_factorial_mul_choose n k
  have key : n ^ k * k.descFactorial k ≤ n.descFactorial k * k ^ k := by
    rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
    have h1 : n ^ k * ∏ i ∈ range k, (k - i) = ∏ i ∈ range k, (n * (k - i)) := by
      rw [prod_mul_distrib, prod_const, card_range]
    have h2 : (∏ i ∈ range k, (n - i)) * k ^ k = ∏ i ∈ range k, ((n - i) * k) := by
      rw [prod_mul_distrib, prod_const, card_range]
    rw [h1, h2]
    apply prod_le_prod'
    intro i hi
    rw [mem_range] at hi
    have e1 : n * (k - i) + n * i = n * k := by
      rw [← mul_add, Nat.sub_add_cancel hi.le]
    have e2 : (n - i) * k + i * k = n * k := by
      rw [← add_mul, Nat.sub_add_cancel (by omega)]
    have e3 : i * k ≤ n * i := by
      rw [mul_comm i k]; exact Nat.mul_le_mul_right i hkn
    omega
  rw [Nat.descFactorial_self, hd] at key
  have hpos : 0 < k.factorial := Nat.factorial_pos k
  have : n ^ k * k.factorial ≤ (n.choose k * k ^ k) * k.factorial := by
    calc n ^ k * k.factorial ≤ k.factorial * n.choose k * k ^ k := key
      _ = (n.choose k * k ^ k) * k.factorial := by ring
  exact Nat.le_of_mul_le_mul_right this hpos

end OMA.E384H1

theorem OMA.solution : OMA.R_Erdos384_erdos_384_R1.H1 := by
  intro n k hk hkn
  by_contra hcon
  push_neg at hcon
  -- hcon : ∀ p, p.Prime → p ∣ n.choose k → n < 2 * p
  have hk_le : k ≤ n := by nlinarith
  have hn16 : 16 < n := by nlinarith
  set C := n.choose k with hC
  have hC0 : C ≠ 0 := (Nat.choose_pos hk_le).ne'
  set S := C.primeFactors with hS
  -- facts about prime factors
  have hbig : ∀ p ∈ S, n < 2 * p := fun p hp =>
    hcon p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  have hint : ∀ p ∈ S, n - k < p ∧ p ≤ n := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ n.descFactorial k := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      exact Dvd.dvd.mul_left (Nat.dvd_of_mem_primeFactors hp) _
    rw [Nat.descFactorial_eq_prod_range] at hpd
    obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finset_prod_iff hpp.prime _).mp hpd
    rw [mem_range] at hi
    obtain ⟨c, hc⟩ := hpi
    have h2 := hbig p hp
    have hp2 := hpp.two_le
    -- n - i = p * c with 0 < n - i < 2p, so c = 1
    have hc1 : c = 1 := by
      rcases Nat.lt_or_ge c 2 with h | h
      · interval_cases c
        · omega
        · rfl
      · have : p * 2 ≤ p * c := Nat.mul_le_mul_left p h
        omega
    subst hc1
    omega
  have hodd : ∀ p ∈ S, p % 2 = 1 ∧ p % 3 ≠ 0 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have h2 := hbig p hp
    constructor
    · by_contra hh
      rcases hpp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero (by omega)) with h | h <;> omega
    · intro h3
      rcases hpp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h3) with h | h <;> omega
  -- C is squarefree, hence C ≤ n ^ |S|
  have hsq : Squarefree C := by
    rw [Nat.squarefree_iff_factorization_le_one hC0]
    intro p
    by_cases hp : p.Prime
    · by_cases hpd : p ∣ C
      · have hmem : p ∈ S := Nat.mem_primeFactors.mpr ⟨hp, hpd, hC0⟩
        have h2 := hbig p hmem
        apply Nat.factorization_choose_le_one
        nlinarith
      · rw [Nat.factorization_eq_zero_of_not_dvd hpd]; omega
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp]; omega
  have hCle : C ≤ n ^ S.card := by
    calc C = ∏ p ∈ S, p := (Nat.prod_primeFactors_of_squarefree hsq).symm
      _ ≤ n ^ S.card := prod_le_pow_card S _ n (fun p hp => (hint p hp).2)
  -- counting: 2 * |S| ≤ k
  have hcount : 2 * S.card ≤ k := by
    have hinj : Set.InjOn (fun p => (n - p) / 2) (S : Set ℕ) := by
      intro p hp q hq hpq
      simp only at hpq
      have := hodd p hp; have := hodd q hq
      have := hint p hp; have := hint q hq
      omega
    rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · have := card_le_card_of_injOn (fun p => (n - p) / 2) (t := range m) (fun p hp => by
        simp only [coe_range, Set.mem_Iio]
        have := hodd p hp; have := hint p hp
        omega) hinj
      rw [card_range] at this
      omega
    · rcases Nat.even_or_odd n with ⟨a, ha⟩ | ⟨a, ha⟩
      · have := card_le_card_of_injOn (fun p => (n - p) / 2) (t := range m) (fun p hp => by
          simp only [coe_range, Set.mem_Iio]
          have := hodd p hp; have := hint p hp
          omega) hinj
        rw [card_range] at this
        omega
      · set j0 := (2 * (n % 3)) % 3 with hj0
        have hj0lt : j0 < m + 1 := by omega
        have := card_le_card_of_injOn (fun p => (n - p) / 2) (t := (range (m + 1)).erase j0)
          (fun p hp => by
            simp only [coe_erase, coe_range, Set.mem_diff, Set.mem_Iio, Set.mem_singleton_iff]
            have := hodd p hp; have := hint p hp
            omega) hinj
        rw [card_erase_of_mem (mem_range.mpr hj0lt), card_range] at this
        omega
  -- final contradiction
  have h1 := OMA.E384H1.pow_le_choose_mul n k hk_le
  have hn1 : 1 ≤ n := by omega
  have h2 : n ^ k ≤ n ^ S.card * k ^ k := le_trans h1 (Nat.mul_le_mul_right _ hCle)
  have h3 : n ^ (2 * k) ≤ n ^ (2 * S.card) * (k * k) ^ k := by
    have := Nat.mul_le_mul h2 h2
    calc n ^ (2 * k) = n ^ k * n ^ k := by ring
      _ ≤ n ^ S.card * k ^ k * (n ^ S.card * k ^ k) := this
      _ = n ^ (2 * S.card) * (k * k) ^ k := by ring
  have h4 : n ^ (2 * S.card) ≤ n ^ k := Nat.pow_le_pow_right hn1 hcount
  have h5 : (k * k) ^ k < n ^ k := Nat.pow_lt_pow_left hkn (by omega)
  have h6 : n ^ (2 * S.card) * (k * k) ^ k < n ^ k * n ^ k := by
    calc n ^ (2 * S.card) * (k * k) ^ k ≤ n ^ k * (k * k) ^ k := Nat.mul_le_mul_right _ h4
      _ < n ^ k * n ^ k := Nat.mul_lt_mul_of_pos_left h5 (by positivity)
  have h7 : n ^ (2 * k) = n ^ k * n ^ k := by ring
  omega
