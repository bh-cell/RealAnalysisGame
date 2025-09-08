import Game.Metadata

World "L2Pset"
Level 2
Title "Problem 2"

Introduction "# Problem 2

Do the same for the exponent $3/2$. Find constants `c`, `d`, and `e` so that:

$(1 + \\frac32 x + c \\cdot x^2 + d \\cdot x^3 + e \\cdot x^4)^2 - (1 + x) ^ 3$

has only terms of degree five or higher.

Hint: when you have multiple existential quantifiers, you can just write a single `use`
and separate the answers by a comma, like so: `use 6, 7, 42` (in place of: `use 6`, then `use 7`, then `use 42`).

"

/-- Find the correct constant. -/
Statement  :
   ∃ c d e, ∀ (x : ℝ),
   (1 + 3 * x / 2 + c * x ^ 2 + d * x ^ 3 + e * x ^ 4) ^ 2
   - (1 + x) ^ 3
    =
    x ^ 5 * (
      3/128 + (11 * x)/512 - (3 * x^2)/1024 + (9 * x^3)/16384
    )
    := by
  use 3 / 8, -1 / 16, 3 / 128
  intro x
  ring_nf



Conclusion "Done."
