import Mathlib

/-!
# OEIS A007837: Gauss congruences for partitions with distinct block sizes

Source: https://oeis.org/A007837
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of partitions of an `n`-set into blocks of pairwise distinct sizes.
Conjecture (OEIS entry; the entry adds a proof via A261599): the Gauss congruences
`a(n p^k) ≡ a(n p^(k-1)) (mod p^k)` hold for all primes `p` and positive integers `n, k`.

Conventions:
* Partitions of `Fin n` are Mathlib's `Finpartition (Finset.univ : Finset (Fin n))`; the block
  sizes are pairwise distinct iff `card` is injective on the blocks.
-/

namespace OMA.S_oeis_a007837

/-- Number of set partitions of `Fin n` with pairwise distinct block sizes. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {P : Finpartition (Finset.univ : Finset (Fin n)) // Set.InjOn Finset.card (P.parts : Set (Finset (Fin n)))}

/-- The Gauss congruences. -/
theorem main : ∀ p n k : ℕ, p.Prime → 1 ≤ n → 1 ≤ k →
    (p : ℤ) ^ k ∣ (a (n * p ^ k) : ℤ) - a (n * p ^ (k - 1)) := by
  sorry

end OMA.S_oeis_a007837
