import Mathlib

/-!
# OEIS A064337: minimal primes with increasing prime differences

Source: https://oeis.org/A064337
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(1) = 2`, `a(2) = 3`, and `a(n+1)` is the least prime `> a(n)` with
`a(n+1) - a(n) > a(n) - a(n-1)`. Conjecture (OEIS entry): `a(n) ~ K n² log n` for some `K`.

Conventions:
* Indexing from `0`: `a 0 = 2`, `a 1 = 3`. `K > 0` is implicit in `~` (`IsEquivalent`).
-/

namespace OMA.S_oeis_a064337

open Filter Asymptotics

/-- The greedy sequence. -/
noncomputable def a : ℕ → ℕ
  | 0 => 2
  | 1 => 3
  | n + 2 => sInf {p : ℕ | p.Prime ∧ a (n + 1) < p ∧ a (n + 1) - a n < p - a (n + 1)}

/-- `a(n) ~ K n² log n`. -/
theorem main : ∃ K : ℝ, 0 < K ∧
    IsEquivalent atTop (fun n : ℕ => (a n : ℝ)) (fun n => K * n ^ 2 * Real.log n) := by
  sorry

end OMA.S_oeis_a064337
