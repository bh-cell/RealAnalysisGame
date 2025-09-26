import Game.Levels.L6Lecture

World "Lecture7"
Level 1
Title "Uniqueness of Limits"

Introduction "
# Level 1

## New Tools You'll Need

`by_contra` and hypothesis name

`abs_pos_of_nonzero`
"

theorem abs_pos_of_nonzero {x : ℝ} (h : x ≠ 0) : 0 < |x| :=
abs_pos.mpr h

/-- If `x ≠ 0`, then `0 < |x|`. -/
TheoremDoc abs_pos_of_nonzero as "abs_pos_of_nonzero" in "Theorems"

NewTheorem abs_pos_of_nonzero

/-- If `a : ℕ → ℝ` converges to `L` and `M`, then `L = M`. -/
TheoremDoc LimUnique as "LimUnique" in "Theorems"

/-- Prove that limits are unique.
-/
Statement LimUnique (a : ℕ → ℝ) (L M : ℝ) (aToL : SeqLim a L) (aToM : SeqLim a M) :
    L = M := by
by_contra h
have f0 : L - M ≠ 0 := by bound
have f1 : 0 < |L - M| := by apply abs_pos_of_nonzero f0
have f2 : 0 < |L - M| / 2 := by bound
specialize aToL (|L - M| / 2) f2
specialize aToM (|L - M| / 2) f2
choose N1 hN1 using aToL
choose N2 hN2 using aToM
have f3 : N1 ≤ N1 + N2 := by bound
have f4 : N2 ≤ N1 + N2 := by bound
specialize hN1 (N1 + N2) f3
specialize hN2 (N1 + N2) f4
have f5 : |L - M| = |(L - a (N1+N2)) + (a (N1 + N2) - M)| := by ring_nf
have f6 : |(L - a (N1+N2)) + (a (N1 + N2) - M)| ≤
    |(L - a (N1+N2))| + |(a (N1 + N2) - M)| := by apply abs_add
have f7 : |(L - a (N1+N2))| = |-(a (N1+N2) - L)| := by ring_nf
have f8 : |-(a (N1+N2) - L)| = |(a (N1+N2) - L)| := by apply abs_neg
linarith [f5, f6, f7, f8, hN1, hN2]

Conclusion ""
