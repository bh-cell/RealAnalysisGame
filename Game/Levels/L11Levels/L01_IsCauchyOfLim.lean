import Game.Levels.L10PsetIntro

World "Lecture11"
Level 1
Title "Big Boss : Limits are Cauchy"


Introduction "
# Level 1: Big Boss - Limits are Cauchy

## New Definition: `IsCauchy`

## New Theorem: `abs_sub_comm` : `|x - y| = |y - x|` (subtraction is commutative inside absolute values)

"

/--
Usage: `have factName : |x - y| = |y - x| := by apply abs_sub_comm`
-/
TheoremDoc abs_sub_comm as "abs_sub_comm" in "Theorems"

NewTheorem abs_sub_comm

/-- For a sequence `a : ℕ → ℝ` is said to satisfy `IsCauchy` (that is, the sequence \"is Cauchy\") if: for every `ε > 0`, there exists `N : ℕ` such that for all `m, n ≥ N`, we have `|a m - a n| < ε`. -/
DefinitionDoc IsCauchy as "IsCauchy"

NewDefinition IsCauchy

def IsCauchy (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, |a m - a n| < ε


/--
If a sequence `a : ℕ → ℝ` converges, then it is Cauchy.
-/
TheoremDoc IsCauchyOfLim as "IsCauchyOfLim" in "Theorems"

/-- Prove this
-/
Statement IsCauchyOfLim (a : ℕ → ℝ) (ha : SeqConv a)
    : IsCauchy a := by
choose L hL using ha
intro ε hε
choose N hN using hL (ε / 2) (by bound)
use N
intro n hn m hm
have hn' : |a n - L| < ε / 2 := by apply hN n hn
have hm' : |a m - L| < ε / 2 := by apply hN m hm
rewrite [(by ring_nf : |a n - a m| = |(a n - L) + (L - a m)|)]
have f1 : |(a n - L) + (L - a m)| ≤ |a n - L| + |L - a m| := by apply abs_add
have f2 : |L - a m| = |a m - L| := by apply abs_sub_comm
linarith [f1, f2, hn', hm']

Conclusion ""
