import GameServer
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

World "L1Pset"
Level 5
Title "Problem 5"

Introduction "
# Problem 5

You've learned about adding hypotheses with `have`, and that you can call tactics not
just to act on the Goal, but  also on hypotheses, via adding `at HypothesisName`.
You also know that calling the `rewrite` tactic on a hypothesis `h : X = Y` takes the *left hand side* `X` and replaces it by `Y`. But what if you needed instead to replace `Y`'s by `X`'s? We call that \"backwards rewriting\". The syntax for that is:

`rewrite [← h]`

or

`rewrite [← h] at h2`

to do it at some other hypothesis, `h2`. You get the backwards arrow by typing \\left,
that is, the backslash, then the word `left`, and then a space.

You will likely find that useful in this problem.
"

/-- Solve the problem -/
Statement (p : ℝ → ℝ) (h1 : ∀ t, p (t) = t ^ 2 + 2 * t)
 (h2 : p (x) = 15)
 :
  ∃ b, x ^ 2 + 2 * x = b := by
  use 15
  specialize h1 x
  rewrite [← h1]
  exact h2

Conclusion "Done."
