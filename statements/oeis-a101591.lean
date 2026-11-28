import Mathlib

/-!
# A101591: Indices k >= 8 designating the k-Somos sequences that first become nonintegral at odd-indexed terms.

Source: https://oeis.org/A101591
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: For every `k >= 8`, the `k`-Somos sequence (with initial terms
`s(0) = ... = s(k - 1) = 1`) first becomes nonintegral at index `2 * k` or `2 * k + 1`.
The entry says the first nonintegral term is at `2k + 1` when `k` is in the sequence and at
`2k` otherwise; `main` states that every term before index `2k` is an integer and that one of
the terms at `2k`, `2k + 1` is not.
-/

namespace OMA.S_oeis_a101591

/-- The `k`-Somos sequence `s_k : ℕ → ℚ` defined by `s_k(n) = 1` for `n < k` and
`s_k(n) = (∑_{j=1}^{⌊k/2⌋} s_k(n - j) * s_k(n - k + j)) / s_k(n - k)` for `n ≥ k`
(the degenerate `k = 0` is set to the constant `1`; only `k ≥ 8` is used). -/
def somos (k : ℕ) (n : ℕ) : ℚ :=
  if h : n < k ∨ k = 0 then 1
  else
    (∑ j ∈ (Finset.Icc 1 (k / 2)).attach,
        somos k (n - j.1) * somos k (n - k + j.1)) / somos k (n - k)
termination_by n
decreasing_by
  all_goals first
    | omega
    | (have := Finset.mem_Icc.mp j.2; omega)

theorem main :
    ∀ k : ℕ, 8 ≤ k →
      (∀ n < 2 * k, (somos k n).den = 1) ∧
        ((somos k (2 * k)).den ≠ 1 ∨ (somos k (2 * k + 1)).den ≠ 1) := by
  sorry

end OMA.S_oeis_a101591
