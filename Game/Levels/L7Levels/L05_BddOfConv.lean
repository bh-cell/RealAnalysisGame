import Game.Levels.L7Levels.L04_FiniteSums

open Finset

World "Lecture7"
Level 6
Title "Bounded"

Introduction "
# Level 6


## New Tools You'll Need

`SeqBdd`

"


/-- A sequence `a : N → ℝ` is bounded (`SeqBdd` holds) if there exists some positive
`M : ℝ` so that `|a n| ≤ M`, for all `n`. -/
DefinitionDoc SeqBdd as "SeqBdd"

NewDefinition SeqBdd

def SeqBdd (a : ℕ → ℝ) : Prop :=
  ∃ M > 0, ∀ n, |a n| ≤ M


/-- If `a : ℕ → ℝ` is a sequence which converges, then it is bounded. -/
TheoremDoc BddOfConv as "BddOfConv" in "Theorems"

/-- Prove this
-/
Statement BddOfConv (a : ℕ → ℝ) (aConv : SeqConv a) :
    SeqBdd a := by

sorry

Conclusion ""
