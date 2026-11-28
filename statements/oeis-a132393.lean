import Mathlib

/-!
# A132393: Triangle of unsigned Stirling numbers of the first kind

Source: https://oeis.org/A132393
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture:
For all `n, m : ℕ` (with `m ≥ 1`), the unsigned Stirling number of the first kind
`T(n + m + 1, m + 1)` equals
`(n + m)! * (∏_{i=1}^m (n + i)^i) * ∑_{n ≥ j_1 ≥ j_2 ≥ ... ≥ j_m ≥ 0} (-1)^(n*m + j_1 + ... + j_m)
  * (∏_{1 ≤ q < p ≤ m} (j_q - j_p + p - q)^2)
  * ∏_{t=1}^m (n + t - 1)_{j_t} / ((n - j_t + t)^(m + 1) * (j_t + m - t)!)`,
where `(x)_k = ∏_{r=0}^{k-1} (x - r)` is the falling factorial.
-/

namespace OMA.S_oeis_a132393

/-- Unsigned Stirling numbers of the first kind `T(n, k)`. -/
def stirlingFirst : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, k + 1 => n * stirlingFirst n (k + 1) + stirlingFirst n k

/-- Falling factorial `(x)_k = ∏_{r=0}^{k-1} (x - r)`. -/
def fallingFact (x : ℚ) (k : ℕ) : ℚ :=
  ∏ r ∈ Finset.range k, (x - (r : ℚ))

/-- Multi-sum identity for unsigned Stirling numbers of the first kind. -/
theorem main :
    ∀ n m : ℕ, 1 ≤ m →
      (stirlingFirst (n + m + 1) (m + 1) : ℚ) =
        (Nat.factorial (n + m) : ℚ) *
        (∏ i ∈ Finset.Icc 1 m, ((n + i : ℕ) : ℚ) ^ i) *
        ∑ j ∈ Finset.univ.filter (fun f : Fin m → Fin (n + 1) => ∀ q p : Fin m, q ≤ p → f p ≤ f q),
          ((-1 : ℚ) ^ (n * m + ∑ t : Fin m, (j t).1)) *
          (∏ q : Fin m, ∏ p ∈ Finset.univ.filter (fun p : Fin m => q < p),
            (((j q).1 : ℚ) - ((j p).1 : ℚ) + (p.1 : ℚ) - (q.1 : ℚ)) ^ 2) *
          (∏ t : Fin m,
            fallingFact ((n + t.1 : ℕ) : ℚ) (j t).1 /
              ((((n - (j t).1 + t.1 + 1 : ℕ) : ℚ) ^ (m + 1)) *
                (Nat.factorial ((j t).1 + m - t.1 - 1) : ℚ))) := by
  sorry

end OMA.S_oeis_a132393
