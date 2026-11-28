import Mathlib

/-!
# A002062: a(n) = Fibonacci(n) + n

Source: https://oeis.org/A002062
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = F(n) + n`, offset 0; the first terms are `0, 2, 3, 5, 7, 10, 14, 20, 29, ...`.

The entry records the conjecture `a(n+2) = A006355(n+4) - A066982(n+1)` (the superscripts in the
entry mark the offsets of the sequences, `0`, `0` and `1`). This file states that claim for all
`n ≥ 0`.

Formalized: `A006355(m)` (binary vectors of length `m` with no singletons, offset 0) is `1` for
`m = 0` and `2 F(m - 1)` otherwise; `A066982(m) = Lucas(m + 1) - (m + 1)` (offset 1), with
`Lucas(k) = F(k - 1) + F(k + 1)` for `k ≥ 1`. Values are taken in `ℤ`.
-/

namespace OMA.S_oeis_a002062

/-- A002062. -/
def a (n : ℕ) : ℤ := Nat.fib n + n

/-- A006355: binary vectors of length `m` containing no singletons. -/
def A006355 (m : ℕ) : ℤ := if m = 0 then 1 else 2 * Nat.fib (m - 1)

/-- Lucas numbers, for `k ≥ 1`. -/
def lucas (k : ℕ) : ℤ := Nat.fib (k - 1) + Nat.fib (k + 1)

/-- A066982: `Lucas(m + 1) - (m + 1)`. -/
def A066982 (m : ℕ) : ℤ := lucas (m + 1) - (m + 1)

theorem main : ∀ n : ℕ, a (n + 2) = A006355 (n + 4) - A066982 (n + 1) := by
  sorry

end OMA.S_oeis_a002062
