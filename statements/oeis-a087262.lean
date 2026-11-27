import Mathlib

/-!
# OEIS A087262: peak over initial value in the `3x + 1` iteration

Source: https://oeis.org/A087262
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A087262 gives the integer quotient of the largest value and the initial value of the `3x + 1`
iteration started at `n`. It is conjectured that if peak/initial value is an integer then it
equals `1`.

Conventions:
* The `3x + 1` map is `x ↦ x/2` (even), `3x + 1` (odd), `n ≥ 1`. The peak of the trajectory is
  `M` when all iterates are `≤ M` and some iterate equals `M` (this needs no assumption on the
  Collatz conjecture). `main`: if the peak `M` is a multiple of `n` then `M = n`.
-/

namespace OMA.S_oeis_a087262

/-- The Collatz map. -/
def T (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else 3 * x + 1

/-- If the peak of the trajectory of `n` is divisible by `n`, it equals `n`. -/
theorem main : ∀ n M : ℕ, 1 ≤ n → (∀ i, T^[i] n ≤ M) → (∃ i, T^[i] n = M) → n ∣ M → M = n := by
  sorry

end OMA.S_oeis_a087262
