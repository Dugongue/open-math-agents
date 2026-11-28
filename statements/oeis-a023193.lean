import Mathlib

/-!
# A023193: largest admissible tuple in `[0, n-1]`

Source: https://oeis.org/A023193
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the largest `k` such that some admissible `k`-tuple taken from `{0, 1, …, n-1}` starts
with `0`. Conjecture (attributed to Dickson): `a(n)` is the largest number of primes that occurs
in infinitely many intervals of `n` consecutive integers.

Conventions:
* A finite set `B` of natural numbers is admissible when for every prime `p` some residue class
  modulo `p` contains no element of `B`.
* "The largest number of primes that occurs in infinitely many intervals of `n` consecutive
  integers" is the largest `k` such that infinitely many `m` have exactly `k` primes in
  `[m, m + n)`. It is written with `sSup`; the set is nonempty and bounded by `n`.
-/

namespace OMA.S_oeis_a023193

/-- Admissible finite sets. -/
def Admissible (B : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ℕ, ∀ b ∈ B, b % p ≠ r % p

/-- `a(n)`, the sequence A023193. -/
noncomputable def a (n : ℕ) : ℕ :=
  sSup {k | ∃ B : Finset ℕ, B ⊆ Finset.range n ∧ 0 ∈ B ∧ Admissible B ∧ B.card = k}

/-- Number of primes in `[m, m + n)`. -/
noncomputable def primesIn (m n : ℕ) : ℕ :=
  ((Finset.Ico m (m + n)).filter Nat.Prime).card

theorem main :
    ∀ n : ℕ, 1 ≤ n → sSup {k | {m | primesIn m n = k}.Infinite} = a n := by
  sorry

end OMA.S_oeis_a023193
