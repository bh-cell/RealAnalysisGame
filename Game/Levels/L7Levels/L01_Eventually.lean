import Game.Levels.L7Levels.L00_Uniqueness

World "Lecture7"
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

"

/-- If `a : ℕ → ℝ` converges to `L`, then there is an `N` so that
for all `n ≥ N`, `|a n| ≥ |L| / 2`. -/
TheoremDoc EventuallyGeHalfLim as "EventuallyGeHalfLim" in "Theorems"

/-- Prove this
-/
Statement EventuallyGeHalfLim (a : ℕ → ℝ) (L : ℝ) (aToL : SeqLim a L) (LneZero: L ≠ 0) :
    ∃ N, ∀ n ≥ N, |L| / 2 ≤ |a n| := by
specialize aToL (|L| / 2)
have : 0 < |L| := by apply abs_pos_of_nonzero LneZero
have : 0 < |L| / 2 := by bound
specialize aToL this
choose N hN using aToL
use N
intro n hn
specialize hN n hn
have l1 : |L| = |a n + (L - a n)| := by ring_nf
have l2 : |a n + (L - a n)| ≤ |a n| + |L - a n| := by apply abs_add
have l3 : |L - a n| = |-(a n - L)| := by ring_nf
have l4 : |-(a n - L)| = |(a n - L)| := by apply abs_neg
linarith [l1, l2, l3, l4, hN]

Conclusion ""

-- Exercise: same but `|a n| ≤ 3 |L| / 2`. Check that it doesn't require `L ≠ 0`...
