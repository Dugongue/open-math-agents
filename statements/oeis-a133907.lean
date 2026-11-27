import Mathlib

/-!
# OEIS A133907: least prime `p` with `C(n+p, p) ≡ 1 (mod p)`

Source: https://oeis.org/A133907
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the least prime `p` such that `C(n+p, p) mod p = 1`. Conjecture (OEIS entry): `a(n)` is
the smallest prime `p` such that `∑_{k=1}^{n} k^(p-1) ≡ n (mod p)`.

Conventions:
* `n ≥ 1`. Both minima are `sInf` over primes; `main` states that they agree.
-/

namespace OMA.S_oeis_a133907

/-- `a(n)`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {p : ℕ | p.Prime ∧ (n + p).choose p % p = 1}

/-- The conjectured characterisation. -/
noncomputable def b (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ (∑ k ∈ Finset.Icc 1 n, k ^ (p - 1)) % p = n % p}

/-- `a(n) = b(n)` for `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = b n := by
  sorry

end OMA.S_oeis_a133907
