import Mathlib

/-!
# OEIS A067590: partitions into odious numbers, asymptotics

Source: https://oeis.org/A067590
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of partitions of `n` into odious numbers (odd binary weight: `1, 2, 4, 7, 8,
…`). Conjecture (OEIS entry): `a(n) ~ c · exp(π √(n/3)) / n^(5/8)` with `c = 0.221864833…`.

Conventions:
* Partitions are Mathlib's `Nat.Partition n`; all parts odious. `c` is read from its quoted digits:
  `0.221864833 ≤ c < 0.221864834`; `~` is `Asymptotics.IsEquivalent`.
-/

namespace OMA.S_oeis_a067590

open Filter Asymptotics

/-- Binary weight. -/
def s2 (k : ℕ) : ℕ := ((Nat.digits 2 k).filter (· = 1)).length

/-- Partitions of `n` into odious parts. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter fun p => ∀ i ∈ p.parts, Odd (s2 i)).card

/-- The conjectured asymptotic. -/
theorem main : ∃ c : ℝ, 0.221864833 ≤ c ∧ c < 0.221864834 ∧
    IsEquivalent atTop (fun n : ℕ => (a n : ℝ))
      (fun n => c * Real.exp (Real.pi * Real.sqrt (n / 3)) / (n : ℝ) ^ ((5 : ℝ) / 8)) := by
  sorry

end OMA.S_oeis_a067590
