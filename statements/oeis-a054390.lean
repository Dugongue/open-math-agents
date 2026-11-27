import Mathlib

/-!
# OEIS A054390: powers of `3` used at most three times

Source: https://oeis.org/A054390
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of ways of writing `n` as a sum of powers of `3`, each power being used at
most three times. Conjecture (OEIS entry): `a(n)` is the number of partitions of `n` into distinct
parts from A038754 (`1, 2, 3, 6, 9, 18, …`: `3^k` and `2·3^k`).

Conventions:
* A representation is a multiplicity function `c : Fin (n+1) → Fin 4` (multiplicity of `3^i`; only
  `3^i ≤ n` matters, and `i ≤ n` suffices) with `∑ c(i) 3^i = n`. A partition into distinct parts
  of A038754 is a finite set of terms of A038754 with sum `n`; the terms are `3^i` and `2·3^i`,
  so it is a pair of subsets `S, T ⊆ {0, …, n}` with `∑_{i ∈ S} 3^i + ∑_{i ∈ T} 2·3^i = n` (these
  values are pairwise distinct).
-/

namespace OMA.S_oeis_a054390

/-- `a(n)`: representations with each power of `3` used at most three times. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 1) → Fin 4)).filter fun c =>
    ∑ i : Fin (n + 1), (c i : ℕ) * 3 ^ (i : ℕ) = n).card

/-- Partitions of `n` into distinct terms of A038754. -/
def b (n : ℕ) : ℕ :=
  (((Finset.range (n + 1)).powerset ×ˢ (Finset.range (n + 1)).powerset).filter fun st =>
    ∑ i ∈ st.1, 3 ^ i + ∑ i ∈ st.2, 2 * 3 ^ i = n).card

/-- The two counts agree. -/
theorem main : ∀ n : ℕ, a n = b n := by
  sorry

end OMA.S_oeis_a054390
