import Mathlib

/-!
# OEIS A070993: `3x + 1` trajectories reaching `n + 1`

Source: https://oeis.org/A070993
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A070993 lists the `n` whose trajectory under the `3x + 1` map reaches `n + 1`. The entry asks
whether this sequence is finite (no further terms below `10⁶`); `main` states that it is finite.

Conventions:
* The `3x + 1` map is `x ↦ x/2` (even), `3x + 1` (odd); `n ≥ 1`, and the trajectory is
  `n, T(n), T²(n), …`.
* The source asks a yes/no question; `main` states the answer yes (finite), and a disproof would
  answer no.
-/

namespace OMA.S_oeis_a070993

/-- The Collatz map. -/
def T (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else 3 * x + 1

/-- Only finitely many `n` have `n + 1` in their trajectory. -/
theorem main : {n : ℕ | 1 ≤ n ∧ ∃ i, T^[i] n = n + 1}.Finite := by
  sorry

end OMA.S_oeis_a070993
