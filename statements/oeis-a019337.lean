import Mathlib

/-!
# A019337: Primes with primitive root 7

Source: https://oeis.org/A019337
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture (Artin's conjecture for 7):
The asymptotic density of primes having `7` as a primitive root among all primes is
Artin's constant `C = ∏_{p prime} (1 - 1 / (p * (p - 1))) ≈ 0.3739558...`.

Conventions:
- `7` is a primitive root modulo prime `p` iff `orderOf (7 : ZMod p) = p - 1`.
-/

namespace OMA.S_oeis_a019337

noncomputable def artinConst : ℝ :=
  ∏' p : {p : ℕ // Nat.Prime p}, (1 - 1 / ((p.1 : ℝ) * ((p.1 : ℝ) - 1)))

noncomputable def primePi (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter Nat.Prime).card

noncomputable def countPrimRoot7 (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter fun p =>
    Nat.Prime p ∧ orderOf (7 : ZMod p) = p - 1).card

theorem main :
    Filter.Tendsto
      (fun N : ℕ => (countPrimRoot7 N : ℝ) / (primePi N : ℝ))
      Filter.atTop (nhds artinConst) := by
  sorry

end OMA.S_oeis_a019337
