import Game.Levels.L4Levels.L04_Cases'

World "Lecture4"
Level 5
Title "AbsLe"

Introduction "
# Level 5

You now know the full And/Or matrix \"Cheat Sheet\":

|           | ∧        | ∨      |
|-----------|----------|--------|
| **Goal**  | `split_ands`    | `left`/`right`  |
| **Hypothesis** | `h.1`, `h.2` | `cases'` |

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

`abs_lt`

"


/-- This says that `|x| < y` if and only if `x < y ∧ -y < x`. -/
TheoremDoc abs_lt as "abs_lt" in "Theorems"

NewTheorem abs_lt


/-- Prove this
-/
Statement (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) :
  ∃ N, ∀ n ≥ N, a n ≥ L - 1 := by
specialize ha 1 (by bound)
choose N hN using ha
use N
intro n hn
specialize hN n hn
rewrite [abs_lt] at hN
have : -1 < a n - L := by apply hN.1
bound

Conclusion ""
