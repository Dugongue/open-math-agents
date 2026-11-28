import Mathlib

/-!
# A092482: Sequence contains no 3-term arithmetic progression, other than its initial terms 1, 2, 3.

Source: https://oeis.org/A092482
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

For n > 2, a(n+2) = 1 + 2^floor(log2(n)) + Sum{k=1..n} (3^A007814(k) + 1)/2
(conjectured and checked up to n=512).
-/

namespace OMA.S_oeis_a092482

noncomputable def nextNoAP (l : List ℕ) : ℕ :=
  sInf {x : ℕ | (∀ y ∈ l, y < x) ∧ ∀ u ∈ l, ∀ v ∈ l, u < v → 2 * v ≠ u + x}

noncomputable def prefSeq : ℕ → List ℕ
  | 0 => [1, 2, 3]
  | n + 1 => prefSeq n ++ [nextNoAP (prefSeq n)]

noncomputable def a (m : ℕ) : ℕ :=
  match m with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | k + 4 => nextNoAP (prefSeq k)

theorem main :
    ∀ n : ℕ, 2 < n →
      a (n + 2) =
        1 + 2 ^ Nat.log 2 n +
          ∑ k ∈ Finset.Icc 1 n, (3 ^ padicValNat 2 k + 1) / 2 := by
  sorry

end OMA.S_oeis_a092482
