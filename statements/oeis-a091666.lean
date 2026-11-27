import Mathlib

/-!
# OEIS A091666: gap after `prime(n)²`

Source: https://oeis.org/A091666
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the difference between `prime(n)²` and the next prime. Conjectures (OEIS entry):
`a(n) ≪ log² n`, and `lim_{N → ∞} (∑_{n ≤ N} a(n)) / (∑_{n ≤ N} log prime(n)) = 2`.

Conventions:
* `prime(n) = Nat.nth Nat.Prime (n - 1)`, `n ≥ 1`; the next prime after `m` is the least prime
  `> m`. `≪` is `IsBigO` as `n → ∞`.
-/

namespace OMA.S_oeis_a091666

open Filter Topology Asymptotics

/-- `prime(n)`. -/
noncomputable def p (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- `a(n)`: next prime after `prime(n)²` minus `prime(n)²`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {q : ℕ | q.Prime ∧ p n ^ 2 < q} - p n ^ 2

/-- Both conjectures. -/
theorem main :
    ((fun n : ℕ => (a n : ℝ)) =O[atTop] fun n => Real.log n ^ 2) ∧
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (a n : ℝ)) / ∑ n ∈ Finset.Icc 1 N, Real.log (p n))
      atTop (𝓝 2) := by
  sorry

end OMA.S_oeis_a091666
