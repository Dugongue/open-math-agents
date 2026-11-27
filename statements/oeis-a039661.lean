import Mathlib

/-!
# OEIS A039661: `e^π` as a series in the nome

Source: https://oeis.org/A039661
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (OEIS entry): `e^π = ∑_{k ≥ 0} A132136(k) / e^(kπ)`, where A132136 is the expansion
`16, 128, 704, 3072, …` of `-λ(t + 1)` in powers of the nome `q = e^(πit)` (`λ` the modular
lambda function).

Conventions:
* With `λ = θ₂⁴/θ₃⁴` and `q ↦ -q` under `t ↦ t + 1`, `-λ(t + 1) = 16 q A(q)⁴ / θ₄(q)⁴`, where
  `A(q) = ∑_{n ≥ 0} q^(n(n+1))` and `θ₄(q) = 1 + 2 ∑_{n ≥ 1} (-1)ⁿ q^(n²)`; this power series in
  `ℤ⟦q⟧` defines A132136 (it reproduces `16, 128, 704, 3072, …`). `θ₄` has constant term `1`.
* A132136 has offset `1`, so its `k`-th term (counting from `k = 0`) is the coefficient of
  `q^(k+1)`; the sum is `∑_{k ≥ 0} [q^(k+1)] (-λ(t+1)) · e^(-kπ)`. (This equals `e^π` exactly
  when `-λ(i + 1) = 1`, i.e. `λ(i) = 1/2`.) The series is read as `HasSum`.
-/

namespace OMA.S_oeis_a039661

open Classical

open PowerSeries

/-- `A(q) = ∑ q^(n(n+1))`. -/
noncomputable def Aser : PowerSeries ℤ :=
  PowerSeries.mk fun m => if ∃ n ∈ Finset.range (m + 1), n * (n + 1) = m then 1 else 0

/-- `θ₄(q) = 1 + 2 ∑_{n ≥ 1} (-1)ⁿ q^(n²)`. -/
noncomputable def theta4 : PowerSeries ℤ :=
  PowerSeries.mk fun m =>
    if m = 0 then 1
    else if ∃ n ∈ Finset.range (m + 1), n ^ 2 = m then 2 * (-1) ^ Nat.sqrt m else 0

/-- `-λ(t+1) = 16 q A⁴/θ₄⁴` as a power series in `q`. -/
noncomputable def G : PowerSeries ℤ := 16 * X * Aser ^ 4 * invOfUnit (theta4 ^ 4) 1

/-- A132136. -/
noncomputable def a (k : ℕ) : ℤ := coeff k G

/-- `∑_{k ≥ 0} a(k+1) e^(-kπ) = e^π`. -/
theorem main :
    HasSum (fun k : ℕ => (a (k + 1) : ℝ) * Real.exp (-(k : ℝ) * Real.pi)) (Real.exp Real.pi) := by
  sorry

end OMA.S_oeis_a039661
