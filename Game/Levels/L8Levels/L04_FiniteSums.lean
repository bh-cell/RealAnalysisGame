import Game.Levels.L7Levels.L03a_Induction'

open Finset

World "Lecture7"
Level 6
Title "Finite Sums"

Introduction "
# Level 6

Finite Sums.
The sum of absolute values exceeds any one absolute value.

## New Tools You'll Need

Summation notation: `∑ k ∈ range N` which means sum as `k` goes from `0` to `N-1` (which has `N` terms!)

`sum_range_succ`

"

/-- If your hypotheses lead to a contradiction, then the `contradiction` tactic closes any goal. -/
TacticDoc contradiction

NewTactic contradiction

/-- Given a function `f : ℕ → ℝ` and a natural number `N`, `sum_range_succ f n` says that:
`∑ n ∈ range (N + 1), f n = ∑ n ∈ range N, f n + f N`. -/
TheoremDoc Finset.sum_range_succ as "sum_range_succ" in "Theorems"


/-- If a function is nonnegative, then its sum is also. -/
TheoremDoc Finset.sum_nonneg as "sum_nonneg" in "Theorems"



NewTheorem Finset.sum_range_succ Finset.sum_nonneg

/-- If `a : ℕ → ℝ` is a sequence, then any term `|a n|`
for `n < N` is less than the sum of all the terms for `n = 0` to `N - 1`. -/
TheoremDoc TermLtSum as "TermLtSum" in "Theorems"

/-- Prove this
-/
Statement TermLtSum (a : ℕ → ℝ) (N : ℕ) :
    ∀ n, n < N → |a n| ≤ ∑ k ∈ range N, |a k| := by
induction' N with N hN
intro n hn
contradiction
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
