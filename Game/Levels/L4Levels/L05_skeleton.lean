import Game.Levels.L3Levels.L04_DoubleSeqConv

World "Lecture3"
Level 5
Title "Big Boss: The Sum of Convergent Sequences"

Introduction ""


/-- For two sequences `a b : ℕ → ℝ` and real numbers `L M : ℝ`, with the hypotheses that `SeqLim a L` and `SeqLim b M`, the theorem `SumLim` says that if
there is a third sequence `c : ℕ → ℝ` so that for all `n`, `c n = a n + b n` (that is, `c` is the sum of the sequences), then `SeqLim c (L + M)` holds. -/
TheoremDoc SumLim as "SumLim" in "Theorems"

/-- Prove that the sum of two convergent sequences converges to the sum of their limits.
This is the mathematician's version of 'if two factories each meet their quality standards, their combined output will too!' -/
Statement SumLim (a b c : ℕ → ℝ) (L M : ℝ)
    (ha : SeqLim a L) (hb : SeqLim b M) (hc : ∀ n, c n = a n + b n) :
    SeqLim c (L + M) := by
sorry


Conclusion ""
