import Game.Levels.L7Levels.L03_SeqInvLim

World "Lecture7"
Level 5
Title "ByCases"

Introduction "
# Level 5

When you already have a hypothesis `h : P ∨ Q`, you can use `cases' h with hP hQ` to
break the goal into two subgoals, the first with the added hypothesis `hP : P` (that `P` is true)
and the second `hQ : Q`.

But how do you break into cases when you don't already have a hypothesis `h`? That's where the `by_cases`
tactic comes in.

## New Tools You'll Need

`by_cases`

"

/-- The `by_cases` tactic has syntax `by_cases h : fact`, where `h` is your name for a new hypothesis,
and `fact` is the fact claimed in the hypothesis. Calling `by_cases` creates two subgoals, one with
the additional hypothesis `h : fact`, and the second has the hypothesis `h : ¬ fact`. -/
TacticDoc by_cases

NewTactic by_cases

/-- If `a : ℕ → ℝ` converges to `L` (with *no* assumption that `L ≠ 0`), then there is an `N` so that
for all `n ≥ N`, `|a (n)| ≥ |L| / 2`. -/
TheoremDoc EventuallyGeHalfLim as "EventuallyGeHalfLim" in "Theorems"


/-- Prove `EventuallyGeHalfLimPos`, but without the assumption that `L ≠ 0`.
-/
Statement EventuallyGeHalfLim (a : ℕ → ℝ) (L : ℝ) (aToL : SeqLim a L) :
    ∃ N, ∀ n ≥ N, |L| / 2 ≤ |a (n)| := by
by_cases h : L = 0
use 1
intro n hn
rewrite [h]
bound
apply EventuallyGeHalfLimPos a L aToL h

Conclusion ""
