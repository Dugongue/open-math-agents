import Mathlib

/-!
# OEIS A134558: `Γ(n+1, k) e^k` as a permanent

Source: https://oeis.org/A134558
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n, k) = Γ(n+1, k) e^k` (upper incomplete gamma). Conjecture (OEIS entry): `a(n, k)` is the
permanent of the `n × n` matrix with `k + 1` on the main diagonal and `1` elsewhere.

Conventions:
* For integers `n, k ≥ 0`, `Γ(n+1, k) e^k = ∑_{j=0}^{n} n!/j! · k^j`, which is used as the
  definition of `a(n, k)`. The permanent is Mathlib's `Matrix.permanent`.
-/

namespace OMA.S_oeis_a134558

/-- `a(n, k) = ∑_{j ≤ n} n!/j! k^j`. -/
def a (n k : ℕ) : ℕ := ∑ j ∈ Finset.range (n + 1), n.factorial / j.factorial * k ^ j

/-- `a(n, k) = perm(J + k I)`. -/
theorem main : ∀ n k : ℕ,
    (Matrix.of fun i j : Fin n => if i = j then (k + 1 : ℕ) else 1).permanent = a n k := by
  sorry

end OMA.S_oeis_a134558
