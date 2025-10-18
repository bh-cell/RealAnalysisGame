import Game.Levels.L12Levels.L01_MonotoneBdd

World "Lecture12"
Level 3
Title "Iterated Gaps"


Introduction "
# Level 3: Iterated Gaps

Now prove the leftover result from the last level.

Goal: `∀ k, k * ε ≤ a (σ^[k] 0) - a 0`.

"

DisabledTheorem IterateGap

/-- Prove `IterateGap`
-/
Statement {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] (a : ℕ → X) (ha : Monotone a) (ε : X)
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
push_cast
linarith [f1, hk, hgap]

Conclusion "
"

#exit

In the next level, we'll prove that if a sequence is monotone (that is, non-decreasing) and bounded above, then it is Cauchy. As a warmup to that, let's prove the following. Suppose that we are given a `Monotone` sequence `a : ℕ → ℝ` and two subsequences, `σ τ : ℕ → ℕ`
with the properties:
- `σ` grows faster than `τ`: `σ n ≥ τ n` for all `n`,
- `τ` grows faster than the identity function: `τ n ≥ n` for all `n`,
- and there is some positive `ε` so that: `ε ≤ |a (σ n) - a (τ n)|`,
that is, the value of `a` on `σ` versus `τ` differs by at least `ε`.

Then the goal is to show that if we iterate `σ` `k` times -- written in Lean as `σ^[k]` -- then we'll grow by at least `k * ε` from the initial value, that is:
