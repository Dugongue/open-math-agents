import Mathlib

/-!
# OEIS A006351: series-parallel networks with n labeled edges

Source: https://oeis.org/A006351

Conjecture in the entry (Kurkov, 2025): `a(n) = A379459(n-2, 0) = A379460(n-1, 0)` for `n > 1`.

Conventions.
- `a` is defined by the recurrence listed in the entry, `a(1) = 1`,
  `a(n) = a(n-1) + ∑_{k=1}^{n-1} C(n-1,k) a(k) a(n-k)` (equivalent to the e.g.f. `A` with
  `A' = (1 + A)/(1 - A)`, `A(0) = 0`, the generating-function characterisation of the count of
  series-parallel networks); `a 0 = 0` is a filler value never used.
- `A379459(n, k) = A379459(n-1, k+1) + 2 (k+1)! ∑_{j ≤ k} A379459(n-1, j) / j!` with
  `A379459(0, k) = 2 (k+1)!` (the divisions `(k+1)!/j!` are exact).
- `A379460(n, k) = A379460(n, k-1) + (k+1) (A379460(n-1, k) + A379460(n-1, k+1))`,
  `A379460(n, 0) = A379460(n-1, 0) + A379460(n-1, 1)`, `A379460(0, k) = 1`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a006351

/-- A006351 via its recurrence. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => a (n + 1) + ∑ k : Fin (n + 1),
      have : (k : ℕ) + 1 < n + 2 := by omega
      have : n + 1 - k < n + 2 := by omega
      (n + 1).choose (k + 1) * a (k + 1) * a (n + 1 - k)

/-- A379459 as a function of the row index `n` and column `k`. -/
def A379459 : ℕ → ℕ → ℕ
  | 0, k => 2 * (k + 1).factorial
  | (n + 1), k => A379459 n (k + 1) +
      2 * ∑ j ∈ Finset.range (k + 1), A379459 n j * ((k + 1).factorial / j.factorial)

/-- Next row of A379460 from the previous row `R`. -/
def nextRow (R : ℕ → ℕ) : ℕ → ℕ
  | 0 => R 0 + R 1
  | (k + 1) => nextRow R k + (k + 2) * (R (k + 1) + R (k + 2))

/-- A379460 as a function of the row index `n` and column `k`. -/
def A379460 : ℕ → ℕ → ℕ
  | 0 => fun _ => 1
  | (n + 1) => nextRow (A379460 n)

theorem main :
    ∀ n : ℕ, 1 < n → a n = A379459 (n - 2) 0 ∧ a n = A379460 (n - 1) 0 := by
  sorry

end OMA.S_oeis_a006351
