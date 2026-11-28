import Mathlib

/-!
# OEIS A005430: Apéry numbers n*C(2n,n)

Source: https://oeis.org/A005430

Conjecture in the entry (Mathar, 2012): the terms of the inverse binomial transform are
`2 * A132894(n)`.

Conventions.
- The inverse binomial transform of `a` is `b(n) = ∑_{k ≤ n} (-1)^(n-k) C(n,k) a(k)`.
- `A132894(n)` is defined as in its entry: the total number of `H = (1,0)` steps over all
  paths of length `n` with steps `U = (1,1)`, `D = (1,-1)`, `H = (1,0)` that start at the origin
  and never go below the x-axis (left factors of Motzkin paths). A path is a word
  `Fin n → Fin 3` with `0 ↦ U`, `1 ↦ D`, `2 ↦ H`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a005430

/-- A005430: `n * C(2n, n)`. -/
def a (n : ℕ) : ℤ := n * (2 * n).choose n

/-- Height change of a step: `U = 0 ↦ +1`, `D = 1 ↦ -1`, `H = 2 ↦ 0`. -/
def stepHeight (s : Fin 3) : ℤ := if s = 0 then 1 else if s = 1 then -1 else 0

/-- The path never goes below the x-axis. -/
def StaysAbove {n : ℕ} (w : Fin n → Fin 3) : Prop :=
  ∀ i ≤ n, 0 ≤ ∑ j : Fin n, if (j : ℕ) < i then stepHeight (w j) else 0

open Classical in
/-- A132894: total number of `H` steps in all length-`n` left factors of Motzkin paths. -/
noncomputable def A132894 (n : ℕ) : ℕ :=
  ∑ w : Fin n → Fin 3, if StaysAbove w then (Finset.univ.filter (fun j => w j = 2)).card else 0

theorem main :
    ∀ n : ℕ, (∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * (n.choose k : ℤ) * a k) =
      2 * (A132894 n : ℤ) := by
  sorry

end OMA.S_oeis_a005430
