import Mathlib

/-!
# A022558: Wilf-equivalence of avoiding 1342 and avoiding {2143, 415263}

Source: https://oeis.org/A022558
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Title: A022558: Number of permutations of length n avoiding the pattern 1342.

Statement:
Conjecture: a(n) is the number of permutations of length n simultaneously avoiding patterns
2143 and 415263.

Conventions:
- A permutation `σ : Equiv.Perm (Fin n)` avoids a pattern `pat : Fin m → ℕ` iff there is no
  strictly increasing subsequence `f : Fin m → Fin n` whose values under `σ` have the same
  relative order as `pat`.
-/

namespace OMA.S_oeis_a022558

/-- Permutation `σ` avoids the pattern `pat`. -/
def AvoidsPattern {n m : ℕ} (σ : Equiv.Perm (Fin n)) (pat : Fin m → ℕ) : Prop :=
  ¬ ∃ f : Fin m → Fin n, StrictMono f ∧ ∀ i j : Fin m, σ (f i) < σ (f j) ↔ pat i < pat j

/-- The pattern 1342. -/
def pat1342 : Fin 4 → ℕ := ![1, 3, 4, 2]

/-- The pattern 2143. -/
def pat2143 : Fin 4 → ℕ := ![2, 1, 4, 3]

/-- The pattern 415263. -/
def pat415263 : Fin 6 → ℕ := ![4, 1, 5, 2, 6, 3]

theorem main :
    ∀ n : ℕ,
      {σ : Equiv.Perm (Fin n) | AvoidsPattern σ pat1342}.ncard =
      {σ : Equiv.Perm (Fin n) | AvoidsPattern σ pat2143 ∧ AvoidsPattern σ pat415263}.ncard := by
  sorry

end OMA.S_oeis_a022558
