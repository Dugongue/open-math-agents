import Mathlib

/-!
# OEIS A078173: solutions of `rst = n(r + s + t)`

Source: https://oeis.org/A078173
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

For the Diophantine equation `r s t = n (r + s + t)` in positive integers `r ≤ s ≤ t`, A078173
gives the maximum of `r`. Conjecture (OEIS entry): the maximum of `t` is `n(n + 2)` and the
maximum of `s` is `2n`, the maxima taken over all positive integer solutions `r ≤ s ≤ t`.

Conventions:
* `n ≥ 1`. Each maximum is stated as: it is attained, and it bounds every solution.
-/

namespace OMA.S_oeis_a078173

/-- `(r, s, t)` is a solution with `1 ≤ r ≤ s ≤ t`. -/
def Sol (n r s t : ℕ) : Prop := 1 ≤ r ∧ r ≤ s ∧ s ≤ t ∧ r * s * t = n * (r + s + t)

/-- `max t = n(n+2)` and `max s = 2n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (∀ r s t, Sol n r s t → t ≤ n * (n + 2)) ∧ (∃ r s, Sol n r s (n * (n + 2))) ∧
    (∀ r s t, Sol n r s t → s ≤ 2 * n) ∧ (∃ r t, Sol n r (2 * n) t) := by
  sorry

end OMA.S_oeis_a078173
