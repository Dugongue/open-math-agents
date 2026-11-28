import Mathlib

/-!
# A077202: a(1) = 1, a(n) = smallest number such that the concatenation of two successive terms gives a prime which has not occurred earlier.

Source: https://oeis.org/A077202
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: Every odd prime occurs in this sequence infinitely many times.
-/

namespace OMA.S_oeis_a077202

/-- Base-10 concatenation of two positive natural numbers `x` and `y`. -/
def concat10 (x y : ℕ) : ℕ :=
  x * 10 ^ (Nat.digits 10 y).length + y

/-- One step of the sequence state `(current term, set of primes formed so far)`. -/
noncomputable def step (st : ℕ × Finset ℕ) : ℕ × Finset ℕ :=
  let m := sInf { m : ℕ | 1 ≤ m ∧ (concat10 st.1 m).Prime ∧ concat10 st.1 m ∉ st.2 }
  (m, insert (concat10 st.1 m) st.2)

/-- The `n`-th term of A077202 (0-indexed, so `a 0 = 1`). -/
noncomputable def a (n : ℕ) : ℕ :=
  (Nat.iterate step n (1, ∅)).1

theorem main :
    ∀ p : ℕ, p.Prime → p ≠ 2 → Set.Infinite { n : ℕ | a n = p } := by sorry

end OMA.S_oeis_a077202
