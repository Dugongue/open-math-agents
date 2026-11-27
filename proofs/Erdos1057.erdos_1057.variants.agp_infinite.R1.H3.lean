import OMAReductions.R_Erdos1057_erdos_1057_variants_agp_infinite_R1

/-! Korselt's criterion (sufficiency): a squarefree composite n with p - 1 dividing n - 1 for
every prime p dividing n is a Carmichael number. -/

-- Step Erdos1057.erdos_1057.variants.agp_infinite.R1.H3: hypothesis H3 of reduction Erdos1057.erdos_1057.variants.agp_infinite.R1
-- Upstream: FormalConjectures/ErdosProblems/1057.lean (Erdos1057.erdos_1057.variants.agp_infinite), reduction R1
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Formalises the classical sufficiency half of Korselt's criterion (A. Korselt, 1899);
-- no new result is claimed.
--
-- Proof idea. Let b be coprime to n and p a prime factor of n. Then p does not divide b, so
-- b ^ (p - 1) = 1 in ZMod p by Fermat, and since p - 1 divides n - 1 also b ^ (n - 1) = 1 there.
-- Hence every prime factor of n divides b ^ (n - 1) - 1, and as n is squarefree it is the product
-- of its prime factors, so n divides b ^ (n - 1) - 1.

namespace OMA_Erdos1057_R1_H3

theorem korselt : OMA.R_Erdos1057_erdos_1057_variants_agp_infinite_R1.H3 := by
  intro n hn hnp hsq hk b hb hcop
  refine ⟨?_, hnp, hn⟩
  unfold Nat.ProbablePrime
  suffices h : (∏ p ∈ n.primeFactors, p) ∣ b ^ (n - 1) - 1 by
    rwa [Nat.prod_primeFactors_of_squarefree hsq] at h
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).prime
  · intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpn := Nat.dvd_of_mem_primeFactors hp
    haveI := Fact.mk hpp
    obtain ⟨k, hk'⟩ := hk p hpp hpn
    have hndvd : ¬ p ∣ b := (Nat.Prime.coprime_iff_not_dvd hpp).mp
      (Nat.Coprime.coprime_dvd_left hpn hcop)
    have hbp : (b : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact hndvd
    have h1 : (b : ZMod p) ^ (n - 1) = 1 := by
      rw [hk', pow_mul, ZMod.pow_card_sub_one_eq_one hbp, one_pow]
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hb), Nat.cast_pow, h1,
      Nat.cast_one, sub_self]

end OMA_Erdos1057_R1_H3

theorem OMA.solution : OMA.R_Erdos1057_erdos_1057_variants_agp_infinite_R1.H3 :=
  OMA_Erdos1057_R1_H3.korselt
