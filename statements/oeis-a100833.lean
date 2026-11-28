import Mathlib

/-!
# A100833: Smallest positive palindrome-free and squarefree sequence.

Source: https://oeis.org/A100833
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture (Robert Israel, Jan 17 2019): `a(n) = 1` if `n ≡ 1 (mod 3)`, `a(n) = 2` if
`n ≡ 2 (mod 3)`, and `a(n) = 3 + v_2(n / 3)` otherwise, where `v_2` is the 2-adic valuation
(A007814).
-/

namespace OMA.S_oeis_a100833

/-- Check whether no suffix of `l` of length at least 2 is a palindrome. -/
def noPalindromeSuffix (l : List ℕ) : Bool :=
  (List.range l.length).all fun i =>
    let suf := l.drop i
    suf.length < 2 || suf != suf.reverse

/-- Check whether no nonempty suffix of `l` is a square `w ++ w`. -/
def noSquareSuffix (l : List ℕ) : Bool :=
  (List.range (l.length / 2)).all fun k =>
    let len := k + 1
    let suf := l.drop (l.length - 2 * len)
    suf.take len != suf.drop len

/-- Greedy prefix `[a(1), ..., a(n)]` of the lexicographically smallest positive
palindrome-free and squarefree sequence. -/
def greedyPrefix : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    let prev := greedyPrefix n
    let bound := prev.foldr max 0 + 1
    let next :=
      ((List.range bound).map (· + 1)).find?
        (fun v => noPalindromeSuffix (prev ++ [v]) && noSquareSuffix (prev ++ [v]))
        |>.getD bound
    prev ++ [next]

/-- The `n`-th term `a(n)` (1-indexed, with `a(0) = 0`). -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else (greedyPrefix n).getLastD 0

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      a n =
        if n % 3 = 1 then 1
        else if n % 3 = 2 then 2
        else 3 + (n / 3).factorization 2 := by
  sorry

end OMA.S_oeis_a100833
