import Mathlib

/-!
# OEIS A105752: `cos(i log(1 + x))` and Stirling numbers of the first kind

Source: https://oeis.org/A105752
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`∑ a(n) xⁿ/n! = cos(i log(1 + x))`. Conjecture (OEIS entry):
`a(n) = ∑_{k=0}^{n} Stirling1(n, 2k)`.

Conventions:
* `cos(i log(1 + x)) = cosh(log(1 + x)) = ((1 + x) + (1 + x)⁻¹)/2`, so
  `a(n) = n! [xⁿ] ((1 + x) + (1 + x)⁻¹)/2`, computed in `ℚ⟦x⟧`.
* `Stirling1` are the signed Stirling numbers of the first kind (A048994),
  `s(n, k) = (-1)^(n-k) c(n, k)` with `c = Nat.stirlingFirst` (unsigned).
-/

namespace OMA.S_oeis_a105752

open PowerSeries

/-- `((1 + x) + (1 + x)⁻¹)/2`. -/
noncomputable def F : PowerSeries ℚ := ((1 + X) + invOfUnit (1 + X) 1) * C (1 / 2 : ℚ)

/-- `a(n) = n! [xⁿ] F`. -/
noncomputable def a (n : ℕ) : ℚ := n.factorial * coeff n F

/-- Signed Stirling numbers of the first kind. -/
def s (n k : ℕ) : ℤ := (-1) ^ (n - k) * (Nat.stirlingFirst n k : ℤ)

/-- `a(n) = ∑_k s(n, 2k)`. -/
theorem main : ∀ n : ℕ, a n = ((∑ k ∈ Finset.range (n + 1), s n (2 * k) : ℤ) : ℚ) := by
  sorry

end OMA.S_oeis_a105752
