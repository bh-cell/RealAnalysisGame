import Game.Levels.L11Levels.L02_IsCauchyOfSum

open Finset

World "Lecture11"
Level 3
Title "Level 3 : Cauchy Implies Bounded"


Introduction "
# Level 3: Cauchy Implies Bounded

"

/--
If a sequence `a` is Cauchy, then it is eventually bounded.
-/
TheoremDoc IsBddOfCauchy as "IsBddOfCauchy" in "Theorems"

/-- Prove this
-/
Statement IsBddOfCauchy (a : ℕ → ℝ) (ha : IsCauchy a)
    : SeqBdd a := by
choose N hN using ha 1 (by bound)
use |a N| + 1 + ∑ k ∈ range N, |a k|
have aNnonneg : 0 ≤ |a N| := by bound
have sumNonneg : 0 ≤ ∑ k ∈ range N, |a k| := by apply sum_nonneg (by bound)
have f1 : ∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k| := by apply TermLeSum a N
split_ands
linarith [aNnonneg, sumNonneg]
intro n
specialize hN N (by bound) n
by_cases hn : n < N
specialize f1 n hn
linarith [f1, aNnonneg]
specialize hN (by bound)
have f2 : |a n| = |(a n - a N) + a N| := by ring_nf
have f3 : |(a n - a N) + a N| ≤ |a n - a N| + |a N| := by apply abs_add
have f4 : |a n - a N| = |a N - a n| := by apply abs_sub_comm
linarith [f2, f3, f4, hN, sumNonneg]

Conclusion ""
