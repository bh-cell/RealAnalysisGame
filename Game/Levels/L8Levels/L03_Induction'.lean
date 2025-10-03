import Game.Levels.L7PsetIntro

World "Lecture8"
Level 1
Title "NotEven"

Introduction "
# Level 1

## New Tools You'll Need

`induction'`

`ge_one_of_nonzero`

"

theorem ge_one_of_nonzero {n : ℕ} (h : n ≠ 0) : 1 ≤ n :=
by omega

/-- If a natural number `n ≠ 0`, then `1 ≤ n`. -/
TheoremDoc ge_one_of_nonzero as "ge_one_of_nonzero" in "Theorems"

NewTheorem ge_one_of_nonzero

/-- The syntax for induction is: `induction' n with k hk`. This means: apply induction on the
variable `n`, use `k` for the new dummy variable (which could be `n` itself), and `hk` for
the induction hypothesis on `k`. -/
TacticDoc induction'

NewTactic induction'

/-- Prove this
-/
Statement (n : ℕ) : n < 2 ^ n := by
induction' n with k hk
norm_num
by_cases hk0 : k = 0
rewrite [hk0]
norm_num
have : 1 ≤ k := by apply ge_one_of_nonzero hk0
have f1 : k + 1 ≤ 2 * k := by bound
have f2 : 2 * k < 2 * 2 ^ k := by linarith [hk]
have f3 : 2 * 2 ^ k = 2 ^ (k + 1) := by ring_nf
linarith [f1, f2, f3]


Conclusion ""
