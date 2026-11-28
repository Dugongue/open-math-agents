import Mathlib

/-!
# A002124: Number of compositions of n into a sum of odd primes

Source: https://oeis.org/A002124
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Statement:
The generating function
`-(z - 1) * (z + 1) * (z^2 + z + 1) * (z^2 - z + 1) / (1 - z^6 - z^3 - z^5 - z^7 + z^9)`
conjectured by Simon Plouffe in his 1992 dissertation for the number of compositions
of `n` into a sum of odd primes is wrong.
-/

namespace OMA.S_oeis_a002124

/-- Number of compositions (ordered tuples) of `n` into odd primes. -/
noncomputable def oddPrimeCompositions (n : ℕ) : ℕ :=
  Nat.card { l : List ℕ // (∀ p ∈ l, Nat.Prime p ∧ Odd p) ∧ l.sum = n }

/-- Ordinary generating function `∑_{n ≥ 0} oddPrimeCompositions n * X^n` in `ℤ[[X]]`. -/
noncomputable def compGF : PowerSeries ℤ :=
  PowerSeries.mk fun n => (oddPrimeCompositions n : ℤ)

/-- Simon Plouffe's 1992 conjectured rational generating function for A002124 is incorrect. -/
theorem main :
    (1 - PowerSeries.X ^ 6 - PowerSeries.X ^ 3 - PowerSeries.X ^ 5 -
      PowerSeries.X ^ 7 + PowerSeries.X ^ 9) * compGF ≠
    -(PowerSeries.X - 1) * (PowerSeries.X + 1) * (PowerSeries.X ^ 2 + PowerSeries.X + 1) *
      (PowerSeries.X ^ 2 - PowerSeries.X + 1) := by
  sorry

end OMA.S_oeis_a002124
