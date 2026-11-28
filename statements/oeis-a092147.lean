import Mathlib

/-!
# A092147: Number of even-length palindromes among the k-tuples of partial quotients of the continued fraction expansions of n/r, r=1,...,n.

Source: https://oeis.org/A092147
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture. Let n=(2^r)(p^s) where p is an odd prime and s>0. Then if p=4k+1, we have
a(n)=2s if r=0, a(n)=4s+1 if r>0. On the other hand, if p=4k+3, we get a(n)=0 if r=0,
a(n)=1 if r>0. Finally, if n=2^r we get a(n)=1.
-/

namespace OMA.S_oeis_a092147

def euclidCF (a b : ℕ) : List ℕ :=
  if h : b = 0 then []
  else (a / b) :: euclidCF b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero h)

def cfExpansions (n r : ℕ) : List (List ℕ) :=
  let l := euclidCF n r
  match l.reverse with
  | x :: rest => if 1 < x then [l, (1 :: (x - 1) :: rest).reverse] else [l]
  | [] => []

def a (n : ℕ) : ℕ :=
  ∑ r ∈ Finset.Icc 1 n,
    ((cfExpansions n r).filter (fun l => l.length % 2 = 0 ∧ l.reverse = l)).length

theorem main :
    (∀ r s p : ℕ, Nat.Prime p → 0 < s → p % 4 = 1 →
      a (2 ^ r * p ^ s) = if r = 0 then 2 * s else 4 * s + 1) ∧
    (∀ r s p : ℕ, Nat.Prime p → 0 < s → p % 4 = 3 →
      a (2 ^ r * p ^ s) = if r = 0 then 0 else 1) ∧
    (∀ r : ℕ, 1 ≤ r → a (2 ^ r) = 1) := by
  sorry

end OMA.S_oeis_a092147
