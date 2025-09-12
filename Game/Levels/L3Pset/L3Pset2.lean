import Game.Levels.L3Pset.L3Pset1

World "L3Pset"
Level 2
Title "Problem 2"

Introduction "# Problem 2"

/-- Prove this. -/
Statement (a : ℕ → ℝ) (ha : ∀ n, a n = (n + 1) / n) :
    SeqConv a := by
use 1
intro ε hε
choose N hN using ArchProp hε
use N
intro n hn
specialize ha n
rewrite [ha]
have : 0 < 1 / ε := by bound
have Npos : (0 : ℝ) < N := by linarith [hN, this]
have : (N : ℝ) ≤ n := by exact_mod_cast hn
have : (0 : ℝ) < n := by linarith [this, Npos]
have : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring_nf
rewrite [this]
have : |(1 : ℝ) / n| = 1 / n := by bound
rewrite [this]
field_simp
field_simp at hN
have : ε * N ≤ ε * n := by bound
linarith [hN, this]

Conclusion "Done."
