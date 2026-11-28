import Mathlib

/-!
# A108600: Number of freely braided permutations of length n; avoiding 3421, 4231, 4312 and 4321.

Source: https://oeis.org/A108600
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: (1-n)*a(n) + (7*n-10)*a(n-1) + 2*(1-4*n)*a(n-2) + 8*(11-2*n)*a(n-3)
+ (n-1)*a(n-4) + 3*(2-n)*a(n-5) + 2*(11-2*n)*a(n-6) = 0.
-/

namespace OMA.S_oeis_a108600

/-- A permutation of `Fin n` is freely braided if it avoids the patterns
`3421`, `4231`, `4312`, and `4321`. -/
def isFreelyBraided {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  (¬ ∃ i j k l : Fin n, i < j ∧ j < k ∧ k < l ∧ σ l < σ k ∧ σ k < σ i ∧ σ i < σ j) ∧
  (¬ ∃ i j k l : Fin n, i < j ∧ j < k ∧ k < l ∧ σ l < σ j ∧ σ j < σ k ∧ σ k < σ i) ∧
  (¬ ∃ i j k l : Fin n, i < j ∧ j < k ∧ k < l ∧ σ k < σ l ∧ σ l < σ j ∧ σ j < σ i) ∧
  (¬ ∃ i j k l : Fin n, i < j ∧ j < k ∧ k < l ∧ σ l < σ k ∧ σ k < σ j ∧ σ j < σ i)

open Classical in
/-- Number of freely braided permutations of length `n`. -/
noncomputable def a (n : ℕ) : ℤ :=
  ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => isFreelyBraided σ)).card : ℤ)

theorem main :
    ∀ n : ℕ, 6 ≤ n →
      (1 - (n : ℤ)) * a n + (7 * (n : ℤ) - 10) * a (n - 1) +
        2 * (1 - 4 * (n : ℤ)) * a (n - 2) + 8 * (11 - 2 * (n : ℤ)) * a (n - 3) +
        ((n : ℤ) - 1) * a (n - 4) + 3 * (2 - (n : ℤ)) * a (n - 5) +
        2 * (11 - 2 * (n : ℤ)) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a108600
