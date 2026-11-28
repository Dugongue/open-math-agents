import Mathlib

/-!
# A005867: a(0) = 1; for n > 0, a(n) = (prime(n)-1)*a(n-1)

Source: https://oeis.org/A005867
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture:
The ordinary generating function for the `prime(n+1)`-rough numbers
(positive integers with no prime factor `< prime(n+1)`) is
`x * P(x) / (1 - x - x^a(n) + x^(a(n)+1))`, where `P(x)` is a polynomial of
degree `a(n)` with symmetric (palindromic) coefficients: `c(i) = c(a(n) - i)`.

Conventions:
- `nthPrime 0 = 2`, `nthPrime 1 = 3`, etc. (0-indexed primes, so `prime(n)` in
  1-indexed OEIS notation is `nthPrime (n - 1)` and `prime(n+1)` is `nthPrime n`).
- `a(0) = 1`, `a(n+1) = (nthPrime n - 1) * a(n)`.
- We state the conjecture for `n ≥ 1`, where `deg(P) = a(n)` and `P` is palindromic.
  (For `n = 0`, the 2-rough numbers are `1, 2, 3, ...`, whose g.f. is `x / (1-x)^2`
  with `P(x) = 1` of degree `0 < a(0) = 1`.)
-/

namespace OMA.S_oeis_a005867

/-- The 0-indexed `n`-th prime (`nthPrime 0 = 2`, `nthPrime 1 = 3`, ...). -/
noncomputable def nthPrime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

/-- A005867: `a(0) = 1`, `a(n+1) = (prime(n+1) - 1) * a(n)` (in 0-indexed prime notation). -/
noncomputable def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => (nthPrime n - 1) * a n

/-- A positive integer `m` is `p`-rough if it has no prime divisor strictly less than `p`. -/
def isRough (p m : ℕ) : Prop :=
  0 < m ∧ ∀ q : ℕ, Nat.Prime q → q < p → ¬ q ∣ m

/-- The 0-indexed sequence of `prime(n+1)`-rough numbers (`roughSeq n 0 = 1`). -/
noncomputable def roughSeq (n k : ℕ) : ℕ :=
  Nat.nth (isRough (nthPrime n)) k

/-- Ordinary generating function `∑_{k ≥ 1} roughSeq n (k - 1) * x^k` in `ℤ[[x]]`. -/
noncomputable def roughGF (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun k => if k = 0 then 0 else (roughSeq n (k - 1) : ℤ)

/-- For every `n ≥ 1`, the generating function of the `prime(n+1)`-rough numbers satisfies
`(1 - x - x^a(n) + x^(a(n)+1)) * roughGF n = x * P(x)` for a palindromic polynomial `P`
of degree `a(n)`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ∃ P : Polynomial ℤ,
        P.natDegree = a n ∧
        (∀ i ≤ a n, P.coeff i = P.coeff (a n - i)) ∧
        (1 - PowerSeries.X - PowerSeries.X ^ a n + PowerSeries.X ^ (a n + 1)) * roughGF n =
          PowerSeries.X * (P : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a005867
