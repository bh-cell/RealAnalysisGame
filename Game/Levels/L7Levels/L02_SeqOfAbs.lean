import Game.Levels.L7Levels.L01_Eventually

World "Lecture7"
Level 3
Title "Eventually"

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

`abs_Lipschitz`
"

theorem abs_Lipschitz {x y : ℝ} : |(|x| - |y|)| ≤ |x - y| :=
by apply abs_abs_sub_abs_le

/-- The absolute value function is Lipschitz with constant 1. -/
TheoremDoc abs_Lipschitz as "abs_Lipschitz" in "Theorems"

NewTheorem abs_Lipschitz

/-- If `a : ℕ → ℝ` converges to `L`, and `b : ℕ → ℝ` is its absolute value, `b n = |a n|` for all `n`, then `b` converges to `|L|`. -/
TheoremDoc AbsLim as "AbsLim" in "Theorems"

/-- Prove this
-/
Statement AbsLim (a : ℕ → ℝ) (L : ℝ) (aToL : SeqLim a L) (b : ℕ →
ℝ) (bEqAbsa : ∀ n, b n = |a n|) :
    SeqLim b |L| := by
intro ε hε
specialize aToL ε hε
choose N hN using aToL
use N
intro n hn
specialize hN n hn
specialize bEqAbsa n
rewrite [bEqAbsa]
have : |(|a n|) - (|L|)| ≤ |a n - L| := by apply abs_Lipschitz
bound



Conclusion ""

-- Exercise : prove `abs_Lipschitz`
