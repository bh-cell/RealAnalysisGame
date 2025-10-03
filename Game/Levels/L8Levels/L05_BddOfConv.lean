import Game.Levels.L8Levels.L04_FiniteSums

open Finset

World "Lecture8"
Level 3
Title "Bounded"

Introduction "
# Level 3

The case `L = 0` will be done in the exercises.

## New Tools You'll Need

def: `SeqBdd`

"

/-- A sequence `a : N → ℝ` is bounded (`SeqBdd` holds) if there exists some positive
`M : ℝ` so that `|a n| ≤ M`, for all `n`. -/
DefinitionDoc SeqBdd as "SeqBdd"

NewDefinition SeqBdd

def SeqBdd (a : ℕ → ℝ) : Prop :=
  ∃ M > 0, ∀ n, |a n| ≤ M

/-- If `a : ℕ → ℝ` is a sequence which converges, then it is bounded. -/
TheoremDoc BddOfConvNonzero as "BddOfConvNonzero" in "Theorems"

/-- Prove this
-/
Statement BddOfConvNonzero (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) (hL : L ≠ 0) :
    SeqBdd a := by
choose N hN using EventuallyBdd_of_SeqConv a L ha hL
use 2 * |L| + ∑ k ∈ range N, |a k|
have absL : 0 < |L| := by apply abs_pos_of_nonzero hL
have f1 : ∀ k ∈ range N, 0 ≤ |a k| := by bound
have f2 : 0 ≤ ∑ k ∈ range N, |a k| := by apply sum_nonneg f1
split_ands
linarith [f2, absL]
intro n
by_cases hn : N ≤ n
specialize hN n hn
linarith [hN, f2]
have hn' : n < N := by bound
have f3 : |a n| ≤ ∑ k ∈ range N, |a k| := by apply TermLtSum a N n hn'
linarith [f3, absL]

Conclusion ""

-- case `L = 0` in exercises
