import OMAReductions.R_Erdos384_erdos_384_R1

/-!
# Erdős Problem 384, reduction R1, step H3: the cases k = 2 and k = 3

Upstream path: reductions/Erdos384.erdos_384.R1.lean, hypothesis H3.
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

This formalises the elementary small cases of Ecklund's theorem
(E. F. Ecklund Jr., Pacific J. Math. 29 (1969)); no new result is claimed.

Proof idea: it suffices to write C(n, k) = F * G with 2 ≤ F and 2F ≤ n; then the
least prime factor of F works.
* k = 2: C(n, 2) = (e / 2) * o, where e is the even one of n, n - 1 and o the other.
* k = 3: split n modulo 6; one of n, n - 1, n - 2 contributes a factor F at most n / 2
  after dividing out the 2 and the 3 (for n = 6m + 1 one takes F = m, which needs
  n ≥ 13, i.e. excludes n = 7).
-/

namespace OMA.E384H3

theorem of_factor (n k F G : ℕ) (h : n.choose k = F * G) (hF : 2 ≤ F) (hF2 : 2 * F ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  refine ⟨F.minFac, Nat.minFac_prime (by omega), ?_, ?_⟩
  · rw [h]; exact Dvd.dvd.mul_right (Nat.minFac_dvd F) G
  · have := Nat.minFac_le (by omega : 0 < F); omega

theorem choose_two_mul (n : ℕ) : n.choose 2 * 2 = n * (n - 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 2
  simp [Nat.descFactorial, Nat.factorial] at h
  rw [mul_comm] at h
  linarith [h]

theorem choose_three_mul (n : ℕ) : n.choose 3 * 6 = n * (n - 1) * (n - 2) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 3
  simp [Nat.descFactorial, Nat.factorial] at h
  rw [show n * (n - 1) * (n - 2) = (n - 2) * ((n - 1) * n) by ring, h]
  ring

theorem case_two (n : ℕ) (hn : 4 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose 2 ∧ 2 * p ≤ n := by
  have h2 := choose_two_mul n
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n = 2m: C(n,2) = m * (2m - 1)
    refine of_factor n 2 m (2 * m - 1) ?_ (by omega) (by omega)
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2)
    rw [h2, hm]
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [show j + 1 + (j + 1) - 1 = 2 * j + 1 by omega, show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
    ring
  · -- n = 2m + 1: C(n,2) = m * (2m + 1)
    refine of_factor n 2 m (2 * m + 1) ?_ (by omega) (by omega)
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2)
    rw [h2, hm, show 2 * m + 1 - 1 = 2 * m by omega]
    ring

theorem case_three (n : ℕ) (hn : 6 ≤ n) (h7 : n ≠ 7) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose 3 ∧ 2 * p ≤ n := by
  have h3 := choose_three_mul n
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 6 ∧ n = 6 * m + r :=
    ⟨n / 6, n % 6, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 6).symm⟩
  interval_cases r
  · -- n = 6m: C = (3m - 1) * (2m (6m - 1)), F = 3m - 1
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    refine of_factor _ 3 (3 * j + 2) ((2 * j + 2) * (6 * j + 5)) ?_ (by omega) (by omega)
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 6)
    rw [h3, show 6 * (j + 1) + 0 - 1 = 6 * j + 5 by omega,
      show 6 * (j + 1) + 0 - 2 = 6 * j + 4 by omega]
    ring
  · -- n = 6m + 1, m ≥ 2: C = m * ((6m + 1)(6m - 1)), F = m
    have hm : 2 ≤ m := by omega
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
    refine of_factor _ 3 (j + 2) ((6 * j + 13) * (6 * j + 11)) ?_ (by omega) (by omega)
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 6)
    rw [h3, show 6 * (j + 2) + 1 - 1 = 6 * j + 12 by omega,
      show 6 * (j + 2) + 1 - 2 = 6 * j + 11 by omega]
    ring
  · -- n = 6m + 2: C = (3m + 1) * (2m (6m + 1)), F = 3m + 1
    refine of_factor _ 3 (3 * m + 1) (2 * m * (6 * m + 1)) ?_ (by omega) (by omega)
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 6)
    rw [h3, show 6 * m + 2 - 1 = 6 * m + 1 by omega, show 6 * m + 2 - 2 = 6 * m by omega]
    ring
  · -- n = 6m + 3: C = (3m + 1) * ((2m + 1)(6m + 1)), F = 3m + 1
    refine of_factor _ 3 (3 * m + 1) ((2 * m + 1) * (6 * m + 1)) ?_ (by omega) (by omega)
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 6)
    rw [h3, show 6 * m + 3 - 1 = 6 * m + 2 by omega, show 6 * m + 3 - 2 = 6 * m + 1 by omega]
    ring
  · -- n = 6m + 4: C = (3m + 2) * ((2m + 1)(6m + 2)), F = 3m + 2
    refine of_factor _ 3 (3 * m + 2) ((2 * m + 1) * (6 * m + 2)) ?_ (by omega) (by omega)
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 6)
    rw [h3, show 6 * m + 4 - 1 = 6 * m + 3 by omega, show 6 * m + 4 - 2 = 6 * m + 2 by omega]
    ring
  · -- n = 6m + 5: C = (3m + 2) * ((6m + 5)(2m + 1)), F = 3m + 2
    refine of_factor _ 3 (3 * m + 2) ((6 * m + 5) * (2 * m + 1)) ?_ (by omega) (by omega)
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 6)
    rw [h3, show 6 * m + 5 - 1 = 6 * m + 4 by omega, show 6 * m + 5 - 2 = 6 * m + 3 by omega]
    ring

end OMA.E384H3

theorem OMA.solution : OMA.R_Erdos384_erdos_384_R1.H3 := by
  intro n k hk2 hk3 hn hne
  interval_cases k
  · exact OMA.E384H3.case_two n (by omega)
  · refine OMA.E384H3.case_three n (by omega) ?_
    rintro rfl
    exact hne rfl
