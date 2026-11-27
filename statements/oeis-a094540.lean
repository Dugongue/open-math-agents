import Mathlib

/-!
# OEIS A094540: last digits of perfect numbers

Source: https://oeis.org/A094540
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the last digit of the `n`-th perfect number. Conjecture (OEIS entry): the ratio of `6`s
to `8`s approaches `1.5`.

Conventions:
* Perfect numbers are Mathlib's `Nat.Perfect`, listed by `Nat.nth`. The ratio after `N` terms is
  `#{n < N | a(n) = 6} / #{n < N | a(n) = 8}`; `main` states that it tends to `3/2` (this
  presupposes infinitely many perfect numbers).
-/

namespace OMA.S_oeis_a094540

open Filter Topology

/-- Last digit of the `n`-th perfect number (from `0`). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth Nat.Perfect n % 10

/-- The ratio of `6`s to `8`s tends to `3/2`. -/
theorem main : Tendsto (fun N : ℕ => (((Finset.range N).filter fun n => a n = 6).card : ℝ) /
    ((Finset.range N).filter fun n => a n = 8).card) atTop (𝓝 (3 / 2)) := by
  sorry

end OMA.S_oeis_a094540
