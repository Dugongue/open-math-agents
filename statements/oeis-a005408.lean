import Mathlib

/-!
# Characterization of primes with one coach via odd-integer permutations (OEIS A005408 / A216371)

Source: https://oeis.org/A005408
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture: A positive integer `b` is a prime with one coach (OEIS A216371),
of the form `4q - 1` or `4q + 1` (`q > 0`), if and only if the top row of its
coach starting at `1` is a permutation of the first `q` odd integers
`{1, 3, ..., 2q - 1}`.

Conventions:
- For an odd integer `b ≥ 3`, the coach transition map on odd integers
  `x ∈ [1, b / 2)` sends `x` to the odd part of `b - x`, namely
  `(b - x) / 2^(v_2(b - x))`.
- `b` has one coach if this map acts transitively on all odd `x < b / 2`
  coprime to `b` (starting from `1`).
-/

namespace OMA.S_oeis_a005408

def coachStep (b x : ℕ) : ℕ :=
  (b - x) / 2 ^ padicValNat 2 (b - x)

def HasOneCoach (b : ℕ) : Prop :=
  ∀ x : ℕ, Odd x → x < b / 2 → Nat.Coprime x b →
    ∃ k : ℕ, (coachStep b)^[k] 1 = x

def InA216371 (b : ℕ) : Prop :=
  Nat.Prime b ∧ 3 ≤ b ∧ HasOneCoach b

theorem main :
    ∀ b : ℕ,
      InA216371 b ↔
        ∃ q : ℕ, 0 < q ∧ (b = 4 * q - 1 ∨ b = 4 * q + 1) ∧
          (Finset.range q).image (fun k => (coachStep b)^[k] 1) =
            (Finset.range q).image (fun i => 2 * i + 1) ∧
          (coachStep b)^[q] 1 = 1 := by
  sorry

end OMA.S_oeis_a005408
