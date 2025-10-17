import Game.Levels.L11Lecture

World "L11Pset"
Level 1
Title "Problem 1"

Introduction "
# Problem 1:

Prove that the sequence `a n = n` has no convergent subsequence.

"

/-- Prove this
-/
Statement (a : ℕ → ℝ) (ha : ∀ n, a n = n)
      : ¬ ∃ σ, Subseq σ ∧ SeqConv (a ∘ σ) := by
sorry

Conclusion "Done."
