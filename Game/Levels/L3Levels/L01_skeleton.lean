import Game.Levels.L2NewtonsCalculationOfPi

open Nat

World "Lecture3"
Level 1
Title "Archimedean Property"

Introduction "
# Level 1: The Archimedean Property

The \"real\" Archimedean Property (which I think is originally due to Eudoxus, and appears already in Euclid's Elements) is that, no matter how small `ε > 0` is, there is
always a natural number `N` so that `1 / N` is even smaller (and of course positive).

Our goal will be to prove the following

Theorem (ArchProp): `(ε : ℝ) (hε : 0 < ε)` : `∃ (N : ℕ), 1 / ε < N`

This is mathematically \"obvious\" but how do you actually do it in Lean?

First let's remember how to do it in natural language.

You need to provide the `N`, so which `N` should we `use`?

The ceiling function `x ↦ ⌈x⌉` rounds up to the nearest integer. (And plus one.) Another thought: use floor and add two.

And this is the WRONG function for this problem. That's because the floor (or ceiling) function
takes values in integers `ℤ` (!!) but we need values in `ℕ`, the naturals.

There is another function written `x ↦ ⌈x⌉₊` (the \"natural number ceiling function\")
which takes any real number and returns a natural number, and what do you think `⌈-3.14⌉₊` is? Answer: `0`.

Now that we know about this function, what's the proof in natural language?

use ⌈1 / ε⌉₊ + 1 (that's a nice natural number)

Our Goal will change to: `1 / ε < ⌈1 / ε⌉₊ + 1`.

We have the fact that `1 / ε ≤ ⌈1 / ε⌉₊` by the definition of this function.

And then we get the strict inequality because we added 1. QED

In Lean, the first two steps in the natural language proof work just fine, but then
we have to deal with casting.

Even when we write the `have` statement to get the fact, look at what Lean produces:

`fact : 1 / ε ≤ ↑⌈1 / ε⌉₊`

There's a weird up arrow `↑`. What is it doing?

You may think of the real numbers as a line, and the natural numbers as a subset of that line, but that is WRONG. We'll learn this more precisely when we get to the construction
of the real numbers, but for now, just know that `ℕ` and `ℤ` and `ℚ` and `ℝ` are all
**different** kinds of things! But there are secret functions that pass what we think of as inclusion around. So the up arrow we see in the Game Board is really a function

`↑ : ℕ → ℝ`

that you should (almost) never even know about. But sometimes Lean doesn't know
what to do, like in this case.

The reason `bound` is failing is this:

after `push_cast`ing, now `bound` works.

## New Tools You'll Need

⌈ ⬝ ⌉₊
casting, `push_cast`
`bound`

"

/-- The `push_cast` tactic handles coercions between number types, particularly useful when working with natural numbers that need to be treated as real numbers (or integers, or rationals). -/
TacticDoc push_cast

/-- The `bound` tactic can solve many \"trivial\" inequalities. -/
TacticDoc bound

NewTactic push_cast bound

/-- Given `ε` and the fact that `0 < ε`, the theorem `ArchProp` claims the existence of `N : ℕ` so that `1 / ε < N`. -/
TheoremDoc ArchProp as "ArchProp" in "Theorems"

/-- Prove the \"Archimedean Property\"
that no matter how small `ε > 0` may be,
there is always an `N` with `1 / ε < N`.
-/
Statement ArchProp {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ), 1 / ε < N := by
use ⌈1 / ε⌉₊ + 1
have fact : 1 / ε ≤ ⌈1 / ε⌉₊ := by bound
push_cast
bound

Conclusion ""
