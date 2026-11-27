import Mathlib

/-!
# OEIS A093600: numerators of coprime harmonic sums

Source: https://oeis.org/A093600
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the numerator of `∑_{1 ≤ k ≤ n, gcd(k, n) = 1} 1/k` and `b(n)` the numerator of
`∑_{1 ≤ k ≤ n, gcd(k, n) = 1} 1/k²`. Conjecture (OEIS entry): if `n^e ∣ a(n)` for some `e > 0`,
then `n^(e-1) ∣ b(n)`.

Conventions:
* `n ≥ 1`, `e ≥ 1` an integer; numerators in lowest terms (`Rat.num`).
-/

namespace OMA.S_oeis_a093600

/-- `∑_{k ≤ n, gcd(k,n)=1} 1/k^s`. -/
def S (s n : ℕ) : ℚ := ∑ k ∈ (Finset.Icc 1 n).filter (fun k => Nat.Coprime k n), (1 : ℚ) / k ^ s

/-- `n^e ∣ a(n) → n^(e-1) ∣ b(n)`. -/
theorem main : ∀ n e : ℕ, 1 ≤ n → 1 ≤ e →
    ((n : ℤ) ^ e ∣ (S 1 n).num) → (n : ℤ) ^ (e - 1) ∣ (S 2 n).num := by
  sorry

end OMA.S_oeis_a093600
