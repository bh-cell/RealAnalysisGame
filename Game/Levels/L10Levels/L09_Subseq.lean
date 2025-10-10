import Game.Levels.L10Levels.L08_Mono

open Finset

World "Lecture10"
Level 4
Title "Subsequence Example"



Introduction "
# Level 4: Subsequence Example

New: the `let` tactic (create something new and name it)

To make a function, the special word is `fun`:

`let f : ℝ → ℝ := fun x ↦ x ^ 2`

"

/-- The `let` tactic is like `have`, but for creating variable names or functions. -/
TacticDoc «let»

NewTactic «let»

/-- Prove this
-/
Statement (a : ℕ → ℝ) (ha : ∀ n, a n = (-1) ^ n) :
    ∃ σ L, Subseq σ ∧ SeqLim (a ∘ σ) L := by
let σ : ℕ → ℕ := fun n ↦ 2 * n
use σ, 1
split_ands
intro i j hij
change 2 * i < 2 * j
linarith [hij]
intro ε hε
use 0
intro n hn
change |a (2 * n) - 1| < ε
specialize ha (2 * n)
rewrite [ha]
have f1 : (-1 : ℝ) ^ (2 * n) = 1 := by bound
rewrite [f1]
norm_num
apply hε

Conclusion ""

-- OrderLimGe in exercises
