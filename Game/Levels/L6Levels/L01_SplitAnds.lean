import Game.Levels.L3Lecture

World "Lecture4"
Level 1
Title "Split Ands"

Introduction "
# Level 1

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

`split_ands`

"

/-- The `split_ands` tactic breaks apart \"and\" Goals into individual pieces. If your goal is `h₁ ∧ h₂ ∧ h₃`, then calling `split_ands` will break that into three separate goals, the first being
`h₁`, the second `h₂`, and of course `h₃`. -/
TacticDoc split_ands

NewTactic split_ands

/-- Prove this
-/
Statement (x y : ℝ) (hx : x = 2) (hy : y = 3) :
    x = 2 ∧ y = 3 := by
split_ands
apply hx
apply hy

Conclusion ""

-- Exercise : `P ∧ Q ∧ R`
