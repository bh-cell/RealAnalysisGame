import Game.Levels.L8Lecture

open Finset

World "Lecture9"
Level 1
Title "Finite Sums"

Introduction "
# Level 1

Finite Sums.
The sum of absolute values exceeds any one absolute value.

Big Hint: Even though the Goal starts with: `∀ n < N`, I suggest you *not* start with
`intro n hn`. Instead, run induction on `N` right from the beginning!

## New Tools You'll Need

Summation notation: `∑ k ∈ range N` which means sum as `k` goes from `0` to `N-1` (which has `N` terms!)

`sum_range_succ`

`sum_nonneg`

`contradiction`

"

/-- If your hypotheses lead to a contradiction, (for example: if one of your hypotheses is that `h : n < 0` where `n : ℕ` is a natural number) then the `contradiction` tactic closes the goal. -/
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
    ∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k| := by
induction' N with N hN
intro n hn
contradiction
intro n hn
have f1 : ∑ k ∈ range (N + 1), |a k| = (∑ k ∈ range N, |a k|) + |a N| := by apply sum_range_succ
rewrite [f1]
by_cases hn' : n < N
specialize hN n hn'
have f1' : 0 ≤ |a N| := by bound
linarith [f1', hN]
have f2 : n = N := by bound
rewrite [f2]
have f3 : ∀ k ∈ range N, 0 ≤ |a k| := by bound
have f4 : 0 ≤ ∑ k ∈ range N, |a k| := by apply sum_nonneg f3
linarith [f4]

Conclusion ""
