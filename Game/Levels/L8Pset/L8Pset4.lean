import Game.Levels.L8Pset.L8Pset3

World "L8Pset"
Level 4
Title "Problem 4"

Introduction "# Problem 4

Suppose a sequence `a : ℕ → ℕ` takes values in the
*natural numbers* (not reals), and is strictly increasing, that is,
if `i < j`, then `a (i) < a (j)`. Prove that
`a (n)` grows at least as fast as `n` itself.

"

/-- Prove the statement. -/
Statement (a : ℕ → ℕ) (ha : ∀ i j, i < j → a (i) < a (j)) : ∀ n, n ≤ a (n)  := by
intro n
induction' n with n hn
bound
have f1 : n < n + 1 := by bound
specialize ha n (n + 1) f1
linarith [hn, f1, ha]

Conclusion ""
