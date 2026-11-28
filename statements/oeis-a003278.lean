import Mathlib

/-!
# A003278: Szekeres's sequence

Source: https://oeis.org/A003278
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) - 1` in ternary is `n - 1` in binary (`n ≥ 1`). Conjecture (L. Edson Jeffery):
`a(n) = (A191107(n) + 2) / 3 = (A055246(n) + 5) / 6`, stated as `3 a(n) = A191107(n) + 2` and
`6 a(n) = A055246(n) + 5`.

Conventions:
* A191107 is the increasing enumeration of the smallest set containing `1` and closed under
  `x ↦ 3x - 2` and `x ↦ 3x + 1`.
* A055246: at step `k ≥ 1` of the Cantor middle-third construction the erased open intervals are
  `(a(n) / 3^k, (1 + a(n)) / 3^k)`, `n = 1, …, 2^(k-1)`. The intervals surviving step `k - 1` are
  `[b / 3^(k-1), (b + 1) / 3^(k-1)]` with `b < 3^(k-1)` having only ternary digits `0, 2`, and their
  open middle thirds have left ends `(3b + 1) / 3^k`. So A055246 is the increasing enumeration of
  the numbers `3b + 1` with `b` having only ternary digits `0, 2`.
* Increasing enumerations use `Nat.nth` (index `n - 1` for the `n`-th term).
-/

namespace OMA.S_oeis_a003278

/-- Szekeres's sequence A003278. -/
def a (n : ℕ) : ℕ := Nat.ofDigits 3 (Nat.digits 2 (n - 1)) + 1

/-- The smallest set containing `1` closed under `x ↦ 3x - 2`, `x ↦ 3x + 1`. -/
def S191107 : Set ℕ :=
  ⋂₀ {T | 1 ∈ T ∧ ∀ x ∈ T, 3 * x - 2 ∈ T ∧ 3 * x + 1 ∈ T}

/-- A191107. -/
noncomputable def a191107 (n : ℕ) : ℕ := Nat.nth (· ∈ S191107) (n - 1)

/-- A055246. -/
noncomputable def a055246 (n : ℕ) : ℕ :=
  Nat.nth (fun x => ∃ b : ℕ, (∀ d ∈ Nat.digits 3 b, d = 0 ∨ d = 2) ∧ x = 3 * b + 1) (n - 1)

theorem main : ∀ n : ℕ, 1 ≤ n → 3 * a n = a191107 n + 2 ∧ 6 * a n = a055246 n + 5 := by
  sorry

end OMA.S_oeis_a003278
