import Game.Levels.L3Levels.L03_NonConverge

World "Lecture3"
Level 4
Title "Doubling a Convergent Sequence"

Introduction "
"

/-- For any real numbers `x` and `y`, we have `|x * y| = |x| * |y|`. -/
TheoremDoc abs_mul as "abs_mul" in "Theorems"

NewTheorem abs_mul


/-- Prove that constant multiples of convergent sequences converge to the constant multiple of the limit.
This is the Machinist's response to scaling demands: 'If you want double the output with the same tolerance, I need half the tolerance on the original process!' -/
Statement (a b : ℕ → ℝ) (L : ℝ)
    (h : SeqLim a L) (b_scaled : ∀ n, b n = 2 * a n) :
    SeqLim b (2 * L) := by
sorry

Conclusion ""
