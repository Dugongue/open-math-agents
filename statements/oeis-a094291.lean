import Mathlib

/-!
# A094291: a(n) = maximal value of C(i, j) * C(n-j, n-i) for 0 <= j <= i <= n.

Source: https://oeis.org/A094291
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture (Hasler): the maximum is attained at i = n - k with k = j or k = j + 1, and
a(n) = C(n-k, j) * C(n-j, k) for some j, k with [n/4] <= j <= k <= j + 1.
-/

namespace OMA.S_oeis_a094291

/-- `a(n)` is the maximum of `C(i, j) * C(n - j, n - i)` over `0 ≤ j ≤ i ≤ n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).biUnion (fun i =>
    (Finset.range (i + 1)).image (fun j =>
      Nat.choose i j * Nat.choose (n - j) (n - i)))).sup id

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ∃ j k : ℕ, n / 4 ≤ j ∧ j ≤ k ∧ k ≤ j + 1 ∧ j + k ≤ n ∧
        a n = Nat.choose (n - k) j * Nat.choose (n - j) k := by
  sorry

end OMA.S_oeis_a094291
