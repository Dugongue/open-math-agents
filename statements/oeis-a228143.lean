import Mathlib

/-!
# OEIS A228143: Hankel determinants of Apéry numbers

Source: https://oeis.org/A228143
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the determinant of the `(n+1) × (n+1)` matrix with `(i, j)` entry `A005259(i+j)`
(`0 ≤ i, j ≤ n`). Conjectures (Sun, OEIS entry): `a(n)/24ⁿ` is always a positive integer; and
`b(n)/10ⁿ` is always a positive integer, where `b(n)` is the analogous Hankel determinant of
A005258.

Conventions:
* `A005259(m) = ∑_k C(m,k)² C(m+k,k)²` and `A005258(m) = ∑_k C(m,k)² C(m+k,k)` (Apéry numbers).
-/

namespace OMA.S_oeis_a228143

/-- A005259. -/
def A3 (m : ℕ) : ℤ := ∑ k ∈ Finset.range (m + 1), ((m.choose k) ^ 2 * ((m + k).choose k) ^ 2 : ℕ)

/-- A005258. -/
def A2 (m : ℕ) : ℤ := ∑ k ∈ Finset.range (m + 1), ((m.choose k) ^ 2 * (m + k).choose k : ℕ)

/-- Hankel determinant of `f` of size `n + 1`. -/
def hankel (f : ℕ → ℤ) (n : ℕ) : ℤ := (Matrix.of fun i j : Fin (n + 1) => f (i + j)).det

/-- Both divisibility-and-positivity conjectures. -/
theorem main : ∀ n : ℕ,
    (∃ z : ℤ, 0 < z ∧ hankel A3 n = 24 ^ n * z) ∧ (∃ z : ℤ, 0 < z ∧ hankel A2 n = 10 ^ n * z) := by
  sorry

end OMA.S_oeis_a228143
