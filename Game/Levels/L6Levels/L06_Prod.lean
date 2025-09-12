import Game.Levels.L5Levels.L05_BddOfConv

open Finset

World "Lecture5"
Level 6
Title "Big Boss : Product of Sequences"



Introduction "
# Level 6

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
/--
`ProdLim`
-/
TheoremDoc ProdLim as "ProdLim" in "Theorems"

/-- Prove this
-/
Statement ProdLim (a b c : ℕ → ℝ) (L M : ℝ) (LneZero : L ≠ 0) (aToL : SeqLim a L) (bToM : SeqLim b M) (cEq : ∀ n, c n = a n * b n):
    SeqLim c (L * M) := by
sorry

Conclusion ""

-- case `L = 0` in exercises
-- general case in exercises!
