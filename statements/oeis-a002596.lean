import Mathlib

/-!
# OEIS A002596: numerators in the expansion of sqrt(1+x)

Source: https://oeis.org/A002596

Observation/conjecture in the entry (Papadopoulos, 2016): if a term is divisible by a prime
`p`, it lies in a block of exactly `(p^k - 3)/2` consecutive terms all divisible by `p`
(for some `k ≥ 1`). Furthermore, if `a(n)` is the term preceding such a block, then
`a(p n - (p-1)/2)` precedes a block of exactly `(p^(k+1) - 3)/2` terms divisible by `p`.

Conventions.
- `a n` is the (signed, reduced) numerator of the coefficient `binom(1/2, n)` of `x^n` in
  `sqrt(1+x)`, written as `∏_{i<n} (1/2 - i) / n!`.
- A block of exactly `L` terms starting at index `s ≥ 1` means `p ∤ a(s-1)`,
  `p ∣ a(s), …, a(s+L-1)` and `p ∤ a(s+L)` (a maximal run).
- In the second part the block is nonempty (`L ≥ 1`), as it is a block from the first part;
  natural-number subtraction is exact there since `p n ≥ (p-1)/2` once `n ≥ 1`, and `n = 0`
  cannot precede a block because `a 1 = 1`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a002596

/-- A002596: numerator of the coefficient of `x^n` in `sqrt(1+x)`. -/
def a (n : ℕ) : ℤ :=
  ((∏ i ∈ Finset.range n, ((1 : ℚ) / 2 - i)) / (n.factorial : ℚ)).num

/-- `a(s), …, a(s+L-1)` is a maximal run of terms divisible by `p`, with `s ≥ 1`. -/
def MaxBlock (p s L : ℕ) : Prop :=
  1 ≤ s ∧ ¬ (p : ℤ) ∣ a (s - 1) ∧ (∀ j < L, (p : ℤ) ∣ a (s + j)) ∧ ¬ (p : ℤ) ∣ a (s + L)

theorem main :
    (∀ p n : ℕ, p.Prime → (p : ℤ) ∣ a n →
      ∃ k s : ℕ, 1 ≤ k ∧ s ≤ n ∧ n < s + (p ^ k - 3) / 2 ∧ MaxBlock p s ((p ^ k - 3) / 2)) ∧
    (∀ p k m : ℕ, p.Prime → 1 ≤ k → 1 ≤ (p ^ k - 3) / 2 → MaxBlock p (m + 1) ((p ^ k - 3) / 2) →
      MaxBlock p (p * m - (p - 1) / 2 + 1) ((p ^ (k + 1) - 3) / 2)) := by
  sorry

end OMA.S_oeis_a002596
