import Game.Levels.L3Levels.L01_ArchProp

open Nat

World "Lecture3"
Level 2
Title "First Real Limit"

Introduction "
# Limit of `1 / n`

We have talked at length about *why* the definition of a limit of a sequence
is what it is. And we proved something trivial, that the constant sequence
does have a limit, namely, the same constant. Let's do something not entirely trivial.

Theorem : `1 / n → 0`.
Proof.
Recall the definition of what it means for a sequence to converge. We have a sequence
`a : ℕ → ℝ`, and we know that `a (n) = 1 / n`, for all `n`. (Really: `1 / ↑n` but nevermind.) The claim that it converges to `L` (for any value of `L`, in this case `L=0`)
is the claim that:

∀ ε > 0, ∃ N, ∀ n ≥ N, |a (n) - L| < ε

Step 1. (Change to the definition.) Let `ε > 0` be given. (`intro ε hε`)

In general, we will want to do some scratch work on paper and this point to figure
out the value of `N` to use. We need `n` to be so large that `|1/n| = 1/n < ε`, i.e.,
multiplying by `n` and dividing by `ε`, this is satisfied as long as `1 / ε < n`.
How do we find an `N` (lower bound) so that this always holds? The Archimedean Property!
By that, we know that there exists some `N` so that `1/ ε < N`, so choose such an `N`.
Use that `N`.
Step 17.
Then let `n ≥ N` be given. New goal:
`|1 / n - 0|< ε`
And we're trivially done. QED.


In Lean, if you don't have context, you can't know what you want to cast it to, e.g.:

`have f2 : |1 / ↑n| = 1 / n`

What kind of cast is that supposed to be?
The way to cast descriptively is with parentheses and a colon.

`have f2 : |1 / (n : ℝ)| = 1 / n`

At this point:

` 1 / ↑n < ε`

You may want to clear denominators with `field_simp` but it won't work, because it
doesn't know how to prove that the denominator is not zero. So we first have to work
up a proof that `n ≠ 0`, or something that will imply it, like `1 ≤ n`.

In Lean, it's (almost) always better to use less than signs than greater that signs.

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
`SeqLim`
`ArchProp`
`bound`
`push_cast`

New:
more on casting `(n : ℝ)`
`field_simp` - like `ring_nf`, but applies to inequalities and tries to clear denominators (if they're known to be positive)
`exact_mod_cast`
Maybe `linarith`?
"

/-- The `linarith` tactic, with syntax `linarith [h₁, h₂]`, can solve goals that are linear arithmetic combinations of hypotheses `h₁, h₂` involving `≤`, `<`, `=` with addition and multiplication by constants.
- ✅ **Linear:** `2*x + y - 3`, `z / 5`
- ❌ **Not Linear:** `x*y`, `x^2`, `|x|`, `1/x`

Example Usage:
h1 : x < y
h2 : y ≤ z
Goal: x < z + 1
linarith [h1, h2]
-/
TacticDoc linarith


/-- The `field_simp` tactic tries to clear denominators, if it can figure out that the denominators are non-zero (or in the case of inequalities, positive). -/
TacticDoc field_simp

/-- The `exact_mod_cast` tactic is similar to `apply`, except
. -/
TacticDoc exact_mod_cast

NewTactic linarith field_simp exact_mod_cast

/-- Prove that `1 / n → 0`.
-/
Statement (a : ℕ → ℝ) (ha : ∀ n, a n = 1 / n) : SeqLim a 0 := by
change ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - 0| < ε
intro ε hε
have f1 : ∃ (N : ℕ), 1 / ε < N := by apply ArchProp hε
choose N eps_inv_lt_N using f1
use N
intro n n_ge_N
ring_nf
specialize ha n
rewrite [ha]
have f2 : |1 / (n : ℝ)| = 1 / n := by bound
rewrite [f2]
have f3 : 0 < 1 / ε := by bound
have Npos : (0 : ℝ) < N := by linarith [f3, eps_inv_lt_N]
have N_le_n : (N : ℝ) ≤ n := by exact_mod_cast n_ge_N
have npos : (0 : ℝ) < n := by linarith [Npos, N_le_n]
field_simp
field_simp at eps_inv_lt_N
have f4 : N * ε ≤ n * ε := by bound
linarith [eps_inv_lt_N, f4]

Conclusion ""
