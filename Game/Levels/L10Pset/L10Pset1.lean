import Game.Levels.L10Lecture

open Finset

World "L10Pset"
Level 1
Title "Problem 1"

Introduction "
# Problem 1:

"
/--
If sequences `a b : ℕ → ℝ` converge with `a` going to `L` and `b` going to `M`,
then the sequence `c n = a n * b n` converges to `L * M`.
-/
TheoremDoc ProdLim as "ProdLim" in "Theorems"

/-- Prove this
-/
Statement ProdLim (a b c : ℕ → ℝ) (L M : ℝ) (ha : SeqLim a L)
    (hb : SeqLim b M) (hc : ∀ n, c n = a n * b n):
    SeqLim c (L * M) := by
sorry

Conclusion ""
