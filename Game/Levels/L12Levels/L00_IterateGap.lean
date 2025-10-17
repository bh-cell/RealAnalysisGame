import Game.Levels.L11Lecture

World "Lecture12"
Level 1
Title "Iterated Gaps"


Introduction "
# Level 1: Iterated Gaps

In the next level, we'll prove that if a sequence is monotone (that is, non-decreasing) and bounded above, then it is Cauchy. As a warmup to that, let's prove the following. Suppose that we are given a `Monotone` sequence `a : ℕ → ℝ` and two subsequences, `σ τ : ℕ → ℕ`
with the properties:
- `σ` grows faster than `τ`: `σ n ≥ τ n` for all `n`,
- `τ` grows faster than the identity function: `τ n ≥ n` for all `n`,
- and there is some positive `ε` so that: `ε ≤ |a (σ n) - a (τ n)|`,
that is, the value of `a` on `σ` versus `τ` differs by at least `ε`.

Then the goal is to show that if we iterate `σ` `k` times -- written in Lean as `σ^[k]` -- then we'll grow by at least `k * ε` from the initial value, that is:

Goal: `∀ k, k * ε ≤ a (σ^[k] 0) - a 0`.

## New definition: `Monotone`

## New tactic: `show` Syntax: `show fact by proof`, for example, if
you want to rewrite by the fact that `|x - y| = |y - x|` without
a separate `have` declaration, you can write:

`rewrite [show |x - y| = |y - x| by apply abs_sub_comm]`

## New theorem: `succ_iterate`

While `σ^[k] (σ n) = σ^[k+1] (n)` is true by definition, it takes
an argument by induction to show that `σ (σ^[k] n) = σ^[k+1] n`. I'll spare you that argument, and give you the theorem `succ_iterate`.

"

/-- The `show` tactic has syntax `show fact by proof`. -/
TacticDoc «show»

NewTactic «show»

/-- A sequence `a : ℕ → X` (where `X` is `ℚ` or `ℝ`) is said to be `Monotone` if `a n ≤ a m` whenever `n ≤ m`. -/
DefinitionDoc Monotone as "Monotone"

NewDefinition Monotone

theorem succ_iterate (σ : ℕ → ℕ) (k : ℕ) (n : ℕ) :
σ (σ^[k] n) = σ^[k+1] n :=
Eq.symm (Function.iterate_succ_apply' σ k n)

/-- For a function `σ : ℕ → ℕ`, we have that: `σ (σ^[k]) = σ^[k+1]`. -/
TheoremDoc succ_iterate as "succ_iterate" in "Theorems"

NewTheorem succ_iterate

/--
If a sequence `a : ℕ → X` (where `X` could be `ℚ` or `ℝ`) is `Monotone` and grows along some subsequences by `ε`, then it eventually grows by `k * ε` for any `k`.
-/
TheoremDoc IterateGap as "IterateGap" in "Theorems"

/-- Prove this
-/
Statement IterateGap {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] (a : ℕ → X) (ha : Monotone a) (ε : X)
  (εpos : ε > 0)
  (τ : ℕ → ℕ) (hτ : ∀ n, τ n ≥ n)
  (σ : ℕ → ℕ) (hσ : ∀ n, σ n ≥ τ n)
  (hgap : ∀ n, ε ≤ |a (σ n) - a (τ n)|)
  : ∀ (k : ℕ), k * ε ≤ a (σ^[k] 0) - a 0
  := by
intro k
induction' k with k hk
norm_num
specialize hgap (σ^[k] 0)
rewrite [(show |a (σ (σ^[k] 0)) - a (τ (σ^[k] 0))| = a (σ (σ^[k] 0)) - a (τ (σ^[k] 0)) by apply abs_of_nonneg (by bound))] at hgap
rewrite [show σ (σ^[k] 0) = σ^[k + 1] 0 by apply succ_iterate] at hgap
have f1 : 0 ≤ a (τ (σ^[k] 0)) - a (σ^[k] 0) := by bound
have f2 : 0 ≤ a (σ^[k] 0) - a 0 := by bound
push_cast
linarith [f1, f2, hk, hgap]

Conclusion "
"
