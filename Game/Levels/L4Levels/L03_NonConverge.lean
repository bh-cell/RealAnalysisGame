import Game.Levels.L3Levels.L02_OneOverN


open Nat Real

World "Lecture3"
Level 3
Title "NonConvergence"

Introduction "
#

Theorem : the sequence `(-1) ^ n` does not converge.

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
`exact_mod_cast`
`field_simp`

New:
negation : `P → ⊥`
`SeqConv`
`abs_add` -- `|x + y| ≤ |x| + |y| := by apply abs_add`
`abs_neg` -- `|-(something)| = |something| := by apply abs_neg`

"

/--
Usage: `have : |x + y| ≤ |x| + |y| := by apply abs_add`
-/
TheoremDoc abs_add as "abs_add" in "Theorems"

/--
Usage: `have : |-x| ≤ |x| := by apply abs_neg`
-/
TheoremDoc abs_neg as "abs_neg" in "Theorems"

NewTheorem abs_add abs_neg

/-- A sequence `a : N → ℝ` converges (`SeqConv a` holds) if there exists some
`L : ℝ` so that `a → L`, that is, `SeqLim a L` holds. -/
DefinitionDoc SeqConv as "SeqConv"

NewDefinition SeqConv

def SeqConv (a : ℕ → ℝ) : Prop :=
  ∃ L, SeqLim a L

/-- Prove that the sequence starting with `a (0) = 2` and continuing by the formula `a (n + 1) = (a (n) + 1) / 2` converges, and determine what it converges to.
-/
Statement (a : ℕ → ℝ) (ha : ∀ n, a n = (-1) ^ n) : ¬ SeqConv a := by
sorry

Conclusion ""
