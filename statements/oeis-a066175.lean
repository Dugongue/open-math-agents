import Mathlib

/-!
# OEIS A066175: `σ(φ(σ(k))) = k`

Source: https://oeis.org/A066175
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A066175 lists the `k` with `σ(φ(σ(k))) = k`. The entry notes that the conjectured infinitude of
Mersenne primes supports the conjecture that this sequence is infinite; `main` states that it is
infinite.
-/

namespace OMA.S_oeis_a066175

open ArithmeticFunction

/-- Infinitely many `k` satisfy `σ(φ(σ(k))) = k`. -/
theorem main : {k : ℕ | ArithmeticFunction.sigma 1 (Nat.totient (ArithmeticFunction.sigma 1 k)) = k}.Infinite := by
  sorry

end OMA.S_oeis_a066175
