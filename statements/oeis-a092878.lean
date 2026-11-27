import Mathlib

/-!
# OEIS A092878: the smallest number in each class of the iterated totient is odd

Source: https://oeis.org/A092878
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

For `n > 0`, class `n` of the iterated Euler `φ` function contains the `k` such that `n`
iterations of `φ` applied to `k` yield `2`. The entry records the conjecture that the smallest
number in class `n` is always odd.

Conventions:
* Class `n` is `{k | φ^[n](k) = 2}` (each `k ≥ 3` lies in exactly one class, since `φ(2) = 1`);
  it contains `3^n` (`φ(3^n) = 2·3^(n-1)`, `φ(2·3^j) = 2·3^(j-1)`), so it is nonempty, and `main`
  states that its least element is odd, for `n ≥ 1`.
-/

namespace OMA.S_oeis_a092878

/-- For `n ≥ 1`, the least `k` with `φ^[n](k) = 2` is odd. -/
theorem main : ∀ n : ℕ, 1 ≤ n → Odd (sInf {k : ℕ | Nat.totient^[n] k = 2}) := by
  sorry

end OMA.S_oeis_a092878
