import Mathlib

/-!
# A095258: a(n+1) is the smallest divisor of (2 + sum of first n terms) but not occurring earlier; a(1) = 1.

Source: https://oeis.org/A095258
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture: integer permutation with inverse A095259: a(A095259(n))=A095259(a(n))=n.
-/

namespace OMA.S_oeis_a095258

/-- Prefix list of the first `n` terms of A095258. -/
noncomputable def prefixList : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | n + 2 =>
    let prev := prefixList (n + 1)
    let nxt := sInf {m : ℕ | 1 ≤ m ∧ m ∉ prev ∧ m ∣ (2 + prev.sum)}
    prev ++ [nxt]

/-- The `n`-th term of A095258 (1-indexed). -/
noncomputable def a (n : ℕ) : ℕ :=
  (prefixList n).getLastD 0

theorem main :
    ∀ m : ℕ, 1 ≤ m → ∃! n : ℕ, 1 ≤ n ∧ a n = m := by
  sorry

end OMA.S_oeis_a095258
