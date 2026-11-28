import Mathlib

/-!
# A103671: Smallest m such that binary representation of n! does not contain m!

Source: https://oeis.org/A103671
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) = smallest m such that the binary representation of n! does not contain m! as a substring.
Conjecture: This sequence is unbounded; for every k there is n with a(n) > k.
-/

namespace OMA.S_oeis_a103671

/-- Smallest `m` such that the binary digits of `m!` do not appear as a contiguous
sublist of the binary digits of `n!`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | ¬ (Nat.digits 2 (Nat.factorial m) <:+: Nat.digits 2 (Nat.factorial n)) }

theorem main :
    ∀ k : ℕ, ∃ n : ℕ, k < a n := by
  sorry

end OMA.S_oeis_a103671
