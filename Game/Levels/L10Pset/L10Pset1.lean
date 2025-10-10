import Game.Levels.L10Lecture

open Finset

World "L10Pset"
Level 1
Title "Problem 1"

Introduction "
# Problem 1:

Assume that the sequence `c` is a suffling of sequences `a` and `b`,
namely, that `(c 0, c 1, c 2, ...) = (a 0, b 0, a 1, b 1, a 2, b 2,...)`.
Assume that the sequence `c` converges.
Prove that the sequences `a` and `b` converge, and to the same thing.

"
/-- Prove this
-/
Statement (a b c : ℕ → ℝ) (hc : ∀ n, c n = if Even n then a (n / 2) else b ((n - 1) / 2))
        (cConv : SeqConv c) : (∃ L, SeqLim a L ∧ SeqLim b L) := by
choose L hL using cConv
use L
split_ands
intro ε hε
choose N hN using hL ε hε


sorry

Conclusion ""
