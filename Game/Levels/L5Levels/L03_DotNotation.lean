import Game.Levels.L4Levels.L02_LeftRight

World "Lecture4"
Level 3
Title "Dot Notation"

Introduction "
# Level 3

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

dot notation

"

/-- Prove this
-/
Statement (x y : ℝ) (h : x = 2 ∧ y = 3) :
    y = 3 := by
apply h.2

Conclusion ""

-- Exercise : `P ∧ Q ∧ R` `h.2.2`.
