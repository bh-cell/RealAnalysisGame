import Game.Levels.L7Levels.L02_SeqOfAbs

World "Lecture7"
Level 4
Title "SeqInvLim"

Introduction "
# Level 4

## New Tools You'll Need

"

/-- If `a : ℕ → ℝ` converges to `L`, and `b : ℕ → ℝ` is its inverse, `b n = 1 / a n` for all `n`, then `b` converges to `1 / L`, provided `L ≠ 0`. -/
TheoremDoc InvLim as "InvLim" in "Theorems"

/-- Prove this
-/
Statement InvLim (a : ℕ → ℝ) (L : ℝ) (aToL : SeqLim a L) (LneZero : L ≠ 0) (b : ℕ →
ℝ) (bEqInva : ∀ n, b n = 1 / a n) :
    SeqLim b (1 / L) := by
choose NhalfL hNhalfL using EventuallyGeHalfLim a L aToL LneZero
intro ε hε
specialize aToL (ε * |L| * |L| / 2) (by positivity)
choose Na hNa using aToL
use Na + NhalfL
intro n hn
specialize bEqInva n
rewrite [bEqInva]
have hnHalfL : NhalfL ≤ n := by bound
have hna : Na ≤ n := by bound
specialize hNhalfL n hnHalfL
specialize hNa n hna
have : 0 < |L| := by apply abs_pos_of_nonzero LneZero
have : 0 < |a n| := by bound
have : a n ≠ 0 := by exact abs_pos.mp this -- bound FAILS
have l1 : |1 / a n - 1 / L| = |(L - a n) / (a n * L)| := by field_simp
have l2 :  |(L - a n) / (a n * L)| =  |(L - a n)| / |(a n * L)| := by apply abs_div
have l3 : |(L - a n)| / |(a n * L)| = |(L - a n)| / (|a n| * |L|) := by bound
have l4 : |L - a n| = |-(a n - L)| := by ring_nf
have l5 : |-(a n - L)| = |(a n - L)| := by apply abs_neg
have l6 : |a n - L| / (|a n| * |L|) < (ε * |L| * |L| / 2) / (|a n| * |L|) := by field_simp; nlinarith
-- linarith [l1, l2, l3, l4, l5, l6]
have := calc
  |1 / a n - 1 / L| = |(L - a n) / (a n * L)| := by apply l1
  _                 = |(L - a n)| / |(a n * L)| := by apply l2
  _                 = |(L - a n)| / (|a n| * |L|) := by apply l3
  _                 = |-(a n - L)| / (|a n| * |L|) := by rewrite [l4]; rfl
  _                 = |(a n - L)| / (|a n| * |L|) := by rewrite [l5]; rfl
  _                 < ε * |L| * |L| / 2 / (|a n| * |L|) := by apply l6
  _                 = ε * |L| / 2 / |a n| := by field_simp
  _                 ≤ ε := by field_simp; bound
apply this


Conclusion ""
