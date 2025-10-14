import Game.Levels.L11Levels.L01_IsCauchyOfLim

World "Lecture11"
Level 2
Title "Level 2 : Sums of Cauchy sequences"


Introduction "
# Level 2: Sums of Cauchy Sequences

"

/--
If sequences `a` and `b` are Cauchy, then so is their sum.
-/
TheoremDoc IsCauchyOfSum as "IsCauchyOfSum" in "Theorems"

/-- Prove this
-/
Statement IsCauchyOfSum (a b : ℕ → ℝ) (ha : IsCauchy a) (hb : IsCauchy b)
    : IsCauchy (a + b) := by
intro ε hε
choose N1 hN1 using ha (ε / 2) (by bound)
choose N2 hN2 using hb (ε / 2) (by bound)
use N1 + N2
intro m hm n hn
specialize hN1 m (by bound) n (by bound)
specialize hN2 m (by bound) n (by bound)
change |(a m + b m) - (a n + b n)| < ε
rewrite [(by ring_nf : |(a m + b m) - (a n + b n)| = |(a m - a n) + (b m - b n)|)]
have f1 : |a m - a n + (b m - b n)| ≤ |a m - a n| + |(b m - b n)| := by apply abs_add
linarith [f1, hN1, hN2]

Conclusion ""
