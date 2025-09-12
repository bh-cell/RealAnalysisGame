import Game.Levels.L5Levels.L03_SeqInvLim

open Finset

World "Lecture5"
Level 4
Title "Finite Sums"



Introduction "
# Level 4

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

`∑ k ∈ range N,`

Finite Sums.
If all terms positive, sum exceeds any term.

`sum_range_succ`

`by_cases`

"

-- `sum_range_succ`

-- `by_cases`


/-- If `a : ℕ → ℝ` is a sequence, then any term `|a n|`
for `n < N` is less than the sum of all the terms for `n = 0` to `N - 1`. -/
TheoremDoc TermLtSum as "TermLtSum" in "Theorems"


/-- Prove this
-/
Statement TermLtSum (a : ℕ → ℝ) (N : ℕ) :
    ∀ n, n < N → |a n| ≤ ∑ k ∈ range N, |a k| := by
induction' N with N hN
intro n hn
exfalso
exact Nat.not_succ_le_zero n hn -- NEEDS WORK!
intro n hn
have : ∑ k ∈ range (N + 1), |a k| = (∑ k ∈ range N, |a k|) + |a N| := by apply sum_range_succ
rewrite [this]
by_cases hn' : n < N
specialize hN n hn'
have : 0 ≤ |a N| := by bound
bound
have : n = N := by bound
rewrite [this]
have : ∀ k ∈ range N, 0 ≤ |a k| := by bound
have : 0 ≤ ∑ k ∈ range N, |a k| := by apply sum_nonneg this
bound

Conclusion ""
