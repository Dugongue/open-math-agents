import Mathlib

/-!
# OEIS A212320: factorials modulo a prime are not all distinct

Source: https://oeis.org/A212320
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Row `n ≥ 2` of A212320 lists `k! mod prime(n)` for `1 < k < prime(n)`. It is conjectured that only
the first and second rows (`prime(n) = 3, 5`) have all terms distinct; i.e. for every prime
`p ≥ 7` the residues `k! mod p`, `1 < k < p`, are not pairwise distinct.
-/

namespace OMA.S_oeis_a212320

/-- For every prime `p ≥ 7`, `k ↦ k! mod p` is not injective on `{2, …, p-1}`. -/
theorem main : ∀ p : ℕ, p.Prime → 7 ≤ p →
    ¬ Set.InjOn (fun k => k.factorial % p) (Set.Ioo 1 p) := by
  sorry

end OMA.S_oeis_a212320
