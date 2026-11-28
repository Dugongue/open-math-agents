import Mathlib

/-!
# A000483: Associated Stirling numbers [[n, 3]]

Source: https://oeis.org/A000483
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjectures:
Let `a(n) = [[n, 3]]` be the number of 3-orbit permutations of an `n`-set with at least
2 elements per orbit (derangements of `Fin n` with 3 cycles).
1. `(n-2)*(n-4)*a(n) - (n-1)*(3*n^2-21*n+35)*a(n-1)
    + (n-1)*(n-2)*(3*n^2-24*n+47)*a(n-2) - (n-5)*(n-1)*(n-2)*(n-3)*(n-4)*a(n-3) = 0`.
2. `3*(-n+4)*a(n) + (9*n^2-59*n+90)*a(n-1) + (-9*n^3+96*n^2-348*n+436)*a(n-2)
    + (n-3)*(3*n^3-45*n^2+237*n-430)*a(n-3) + 5*(n-5)*(n-6)*(n-3)*(n-4)*a(n-4) = 0`.
-/

namespace OMA.S_oeis_a000483

/-- Second-order reciprocal (associated) Stirling number `[[N, k]]`:
number of fixed-point-free permutations of `Fin N` with exactly `k` cycles. -/
noncomputable def assocStirling (N k : ℕ) : ℕ :=
  Nat.card { σ : Equiv.Perm (Fin N) // (∀ x : Fin N, σ x ≠ x) ∧ σ.cycleType.card = k }

/-- A000483: `a(n) = [[n, 3]]`. -/
noncomputable def a (n : ℕ) : ℤ :=
  (assocStirling n 3 : ℤ)

/-- Both conjectured linear recurrences for `a(n) = [[n, 3]]` hold for all `n ≥ 6`. -/
theorem main :
    ∀ n : ℕ, 6 ≤ n →
      (((n : ℤ) - 2) * ((n : ℤ) - 4) * a n -
        ((n : ℤ) - 1) * (3 * (n : ℤ) ^ 2 - 21 * (n : ℤ) + 35) * a (n - 1) +
        ((n : ℤ) - 1) * ((n : ℤ) - 2) * (3 * (n : ℤ) ^ 2 - 24 * (n : ℤ) + 47) * a (n - 2) -
        ((n : ℤ) - 5) * ((n : ℤ) - 1) * ((n : ℤ) - 2) * ((n : ℤ) - 3) * ((n : ℤ) - 4) * a (n - 3) = 0) ∧
      (3 * (-(n : ℤ) + 4) * a n +
        (9 * (n : ℤ) ^ 2 - 59 * (n : ℤ) + 90) * a (n - 1) +
        (-9 * (n : ℤ) ^ 3 + 96 * (n : ℤ) ^ 2 - 348 * (n : ℤ) + 436) * a (n - 2) +
        ((n : ℤ) - 3) * (3 * (n : ℤ) ^ 3 - 45 * (n : ℤ) ^ 2 + 237 * (n : ℤ) - 430) * a (n - 3) +
        5 * ((n : ℤ) - 5) * ((n : ℤ) - 6) * ((n : ℤ) - 3) * ((n : ℤ) - 4) * a (n - 4) = 0) := by
  sorry

end OMA.S_oeis_a000483
