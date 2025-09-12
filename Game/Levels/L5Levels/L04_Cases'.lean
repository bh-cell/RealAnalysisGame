import Game.Levels.L4Levels.L03_DotNotation

World "Lecture4"
Level 4
Title "Cases'"

Introduction "
# Level 4

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

`cases'` -- make this called `cases`!!

"


/-- When have a hypothesis `h : P ∨ Q`, you can say `cases' h with h1 h2`; this will make two new Game Boards, one with an extra hypothesis `h1 : P`, and the other with the hypothesis `h2 : Q`. You'll have to solve both to solve the original Goal! -/
TacticDoc cases'

NewTactic cases'


/-- Prove this
-/
Statement (x y : ℝ) (h : x = 2 ∨ y = 3) :
    (x - 2) * (y - 3) = 0 := by
cases' h with h1 h2
rewrite [h1]
ring_nf
rewrite [h2]
ring_nf


Conclusion "
"
