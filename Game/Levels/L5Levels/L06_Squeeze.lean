import Game.Levels.L4Levels.L05_AbsLt

World "Lecture4"
Level 6
Title "Big Boss : Squeeze Theorem"

Introduction "
# Level 6 Big Boss : Squeeze Theorem

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


"


/-- If `a c : ℕ → ℝ`, with `a` and `c` both converging to `L`,
and `b` is another sequence, squeezed between `a` and `c`, then `b` also converges to `L`. -/
TheoremDoc SqueezeThm as "SqueezeThm" in "Theorems"


/-- Prove this
-/
Statement SqueezeThm (a b c : ℕ → ℝ) (L : ℝ) (aToL : SeqLim a L)
(cToL : SeqLim c L) (aLeb : ∀ n, a n ≤ b n) (bLec : ∀ n, b n ≤ c n) :
  SeqLim b L := by
intro ε hε
specialize aToL ε hε
specialize cToL ε hε
choose Na hNa using aToL
choose Nc hNc using cToL
use Na + Nc
intro n hn
have hna : Na ≤ n := by bound
have hnc : Nc ≤ n := by bound
specialize hNa n hna
specialize hNc n hnc
rewrite [abs_lt] at hNa
rewrite [abs_lt] at hNc
rewrite [abs_lt]
split_ands
specialize aLeb n
bound
specialize bLec n
bound


Conclusion ""
