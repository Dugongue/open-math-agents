import Mathlib

/-!
# OEIS A060941: Duchon's numbers, a supercongruence

Source: https://oeis.org/A060941
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Duchon's number `a(n)` is the number of paths of length `5n` from the origin to the line
`y = 2x/3` with unit East and North steps that stay below the line or touch it. Let `A(x)` be
their generating function and `b(n) = [xⁿ] A(x)ⁿ` (`1, 2, 50, 1415, …`).
Conjecture (P. Bala, OEIS entry): `b(p) ≡ b(1) (mod p³)` for every prime `p ≥ 7`.

Conventions:
* A path is a word `w : Fin (5n) → Bool` (`true` = East step). After `5n` steps it is on the line
  `y = 2x/3` iff it has `3n` East steps; it stays weakly below the line iff every prefix with `e`
  East and `u` North steps has `3u ≤ 2e`.
* The entry's later, more general supercongruence conjectures are not included.
-/

namespace OMA.S_oeis_a060941

open PowerSeries

/-- Number of East steps among the first `k` steps of `w`. -/
def east {m : ℕ} (w : Fin m → Bool) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k ∧ w i = true)).card

/-- Number of North steps among the first `k` steps of `w`. -/
def north {m : ℕ} (w : Fin m → Bool) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k ∧ w i = false)).card

/-- Duchon's number `a(n)`. -/
def duchon (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin (5 * n) → Bool =>
    east w (5 * n) = 3 * n ∧ ∀ k ≤ 5 * n, 3 * north w k ≤ 2 * east w k)).card

/-- The generating function `A(x) = ∑ a(n) xⁿ`. -/
def A : PowerSeries ℤ :=
  PowerSeries.mk fun n => (duchon n : ℤ)

/-- `b(n) = [xⁿ] A(x)ⁿ`. -/
noncomputable def b (n : ℕ) : ℤ :=
  coeff n (A ^ n)

/-- Bala's supercongruence `b(p) ≡ b(1) (mod p³)` for primes `p ≥ 7`. -/
theorem main : ∀ p : ℕ, p.Prime → 7 ≤ p → b p ≡ b 1 [ZMOD (p : ℤ) ^ 3] := by
  sorry

end OMA.S_oeis_a060941
