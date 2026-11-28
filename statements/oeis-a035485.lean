import Mathlib

/-!
# A035485: R. K. Guy's shuffling problem

Source: https://oeis.org/A035485
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Start with the deck `1, 2, 3, …`. At the `n`-th step, pick up the top `n` cards and interlace
them with the next `n`: the deck after step 1 is `2, 1, 3, …`, after step 2 `3, 2, 4, 1, 5, …`,
after step 3 `1, 3, 5, 2, 6, 4, 7, …`. `a(n)` is the top card after step `n`.
Conjecture: eventually every number appears on top of the deck.

Convention: a deck is a map position (from `0`, the top) ↦ card. Step `n` sends a deck `d` to
`d'` with `d'(2i) = d(n + i)` and `d'(2i + 1) = d(i)` for `i < n`, and `d'(j) = d(j)` for `j ≥ 2n`.
"Eventually every number appears on top" is read as: every card is on top after some step.
-/

namespace OMA.S_oeis_a035485

/-- One step of the shuffle. -/
def step (n : ℕ) (d : ℕ → ℕ) : ℕ → ℕ := fun j =>
  if j < 2 * n then (if j % 2 = 0 then d (n + j / 2) else d (j / 2)) else d j

/-- The deck after `n` steps. -/
def deck : ℕ → ℕ → ℕ
  | 0 => fun j => j + 1
  | n + 1 => step (n + 1) (deck n)

theorem main : ∀ c : ℕ, 1 ≤ c → ∃ n, deck n 0 = c := by
  sorry

end OMA.S_oeis_a035485
