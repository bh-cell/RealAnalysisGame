import Game.Levels.L4Levels.L01_SplitAnds

World "Lecture4"
Level 2
Title "Left and Right"

Introduction "
# Level 2

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

`left` and `right`

"

/-- When your goal is to prove an \"Or\" statement, `P ∨ Q`, you can do that by proving either `P` or `Q`. If you want to prove `P`, then say `left`, and the Goal will turn into `P`. -/
TacticDoc left

/-- When your goal is to prove an \"Or\" statement, `P ∨ Q`, you can do that by proving either `P` or `Q`. If you want to prove `Q`, then say `right`, and the Goal will turn into `Q`. -/
TacticDoc right

NewTactic left right

/-- Prove this
-/
Statement (x y : ℝ) (hx : x = 2) (hy : y = 3) :
    x = 3 ∨ y = 3 := by
right
apply hy

Conclusion ""
