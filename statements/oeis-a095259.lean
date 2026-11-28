import Mathlib

/-!
# A095259: Smallest m such that A095258(m) = n.

Source: https://oeis.org/A095259
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Inverse of A095258, if the conjecture is true, that this is a permutation:
a(A095258(n)) = A095258(a(n)) = n.
-/

namespace OMA.S_oeis_a095259

/-- Prefix list of the first `n` terms of A095258. -/
noncomputable def prefixA095258 : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | n + 2 =>
    let prev := prefixA095258 (n + 1)
    let nxt := sInf {m : ℕ | 1 ≤ m ∧ m ∉ prev ∧ m ∣ (2 + prev.sum)}
    prev ++ [nxt]

/-- The `n`-th term of A095258 (1-indexed). -/
noncomputable def a095258 (n : ℕ) : ℕ :=
  (prefixA095258 n).getLastD 0

/-- The `n`-th term of A095259 (1-indexed): smallest `m ≥ 1` with `A095258(m) = n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ a095258 m = n}

theorem main :
    ∀ n : ℕ, 1 ≤ n → a (a095258 n) = n ∧ a095258 (a n) = n := by
  sorry

end OMA.S_oeis_a095259
