import Game.Levels.L5Levels.L04_FiniteSums

open Finset

World "Lecture5"
Level 5
Title "Bounded"



Introduction "
# Level 5

Existing tools:
`apply`
`change`
`choose`
`have`
`intro`
`norm_num`
`rewrite`
`rfl`
`ring_nf`
`specialize`
`use`


## New Tools You'll Need


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
