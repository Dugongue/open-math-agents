import Mathlib

/-!
# OEIS A133154: Granville's conjecture on `m^j + j ≡ 0 (mod p)`

Source: https://oeis.org/A133154
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

For a prime `p`, A133154 gives the smallest `m ≤ p - 1` such that `j = p - 1` is the only
`j ∈ [1, 2p]` with `m^j + j ≡ 0 (mod p)`. Conjecture (Granville): for every prime `p` such an `m`
exists, i.e. for some `1 ≤ m ≤ p - 1` there is no `j ∈ [1, 2p]` other than `j = p - 1` with
`m^j + j ≡ 0 (mod p)`.

Conventions:
* `m^(p-1) + (p - 1) ≡ 1 - 1 = 0` holds for every `1 ≤ m ≤ p - 1` (Fermat), so the content is the
  absence of other `j`. Congruences are in `ZMod p`.
-/

namespace OMA.S_oeis_a133154

/-- For every prime `p` some `1 ≤ m ≤ p - 1` has `m^j + j ≢ 0` for all `j ∈ [1, 2p]`,
`j ≠ p - 1`. -/
theorem main : ∀ p : ℕ, p.Prime → ∃ m : ℕ, 1 ≤ m ∧ m ≤ p - 1 ∧
    ∀ j ∈ Finset.Icc 1 (2 * p), j ≠ p - 1 → ((m : ZMod p) ^ j + j ≠ 0) := by
  sorry

end OMA.S_oeis_a133154
