import Game.Levels.L5Levels.L01_Eventually

World "Lecture5"
Level 2
Title "Eventually"

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

`abs_abs_sub_abs_le` ??? Hopefully not
"

/-- If `a : ℕ → ℝ` converges to `L`, and `b : ℕ → ℝ` is its absolute value, `b n = |a n|` for all `n`, then `b` converges to `L`. -/
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
have : |(|a n|) - (|L|)| ≤ |a n - L| := by apply abs_abs_sub_abs_le -- bound FAILS
bound

Conclusion ""
