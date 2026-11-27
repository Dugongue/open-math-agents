import Mathlib

/-!
# OEIS A060693: Schröder paths by number of peaks

Source: https://oeis.org/A060693
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`T(n, k)` is the number of Schröder paths from `(0, 0)` to `(2n, 0)` with `k` peaks. Conjecture
(OEIS entry): `∑_{k=0}^{n} (-1)^k T(n, k) (n + 1 - k)² = 1 + n + n²`.

Conventions:
* A Schröder path uses steps `U = (1, 1)`, `D = (1, -1)`, `F = (2, 0)` (coded `0, 1, 2`), never
  goes below the axis, and ends at `(2n, 0)`. A peak is a `U` immediately followed by a `D`.
  A path to `(2n, 0)` has at most `2n` steps, so `T(n, k)` counts step lists of length `≤ 2n`.
-/

namespace OMA.S_oeis_a060693

/-- Horizontal length of a step. -/
def dx (s : Fin 3) : ℕ := if s = 2 then 2 else 1

/-- Height change of a step. -/
def dy (s : Fin 3) : ℤ := if s = 0 then 1 else if s = 1 then -1 else 0

/-- `w : Fin L → Fin 3` is a Schröder path to `(2n, 0)`. -/
def IsSchroeder (n L : ℕ) (w : Fin L → Fin 3) : Prop :=
  ∑ i, dx (w i) = 2 * n ∧ ∑ i, dy (w i) = 0 ∧
    ∀ m ≤ L, 0 ≤ ∑ i : Fin L, if (i : ℕ) < m then dy (w i) else 0

/-- Number of peaks (`U` followed by `D`). -/
def peaks {L : ℕ} (w : Fin L → Fin 3) : ℕ :=
  (Finset.univ.filter fun i : Fin L => ∃ h : (i : ℕ) + 1 < L, w i = 0 ∧ w ⟨i + 1, h⟩ = 1).card

/-- `T(n, k)`. -/
noncomputable def T (n k : ℕ) : ℕ :=
  ∑ L ∈ Finset.range (2 * n + 1),
    {w : Fin L → Fin 3 | IsSchroeder n L w ∧ peaks w = k}.ncard

/-- The conjectured alternating sum. -/
theorem main : ∀ n : ℕ,
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (T n k : ℤ) * ((n : ℤ) + 1 - k) ^ 2 = ((1 + n + n ^ 2 : ℕ) : ℤ) := by
  sorry

end OMA.S_oeis_a060693
