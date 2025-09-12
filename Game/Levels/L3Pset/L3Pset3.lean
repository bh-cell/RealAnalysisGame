import Game.Levels.L3Pset.L3Pset2

World "L3Pset"
Level 3
Title "Problem 3"

Introduction "# Problem 3"


/-- Prove this. -/
Statement (a : ℕ → ℝ) (ha : ∀ n, a n = (3 * n + (-1) ^ n) / (2 * n + 5)) :
    SeqConv a := by
use 3 / 2
intro ε hε
choose N hN using ArchProp (by bound : 0 < 4 * ε / 17)
have Npos : (0 : ℝ) < N := by sorry --- positivity -- bound --linarith
field_simp at hN
use N
intro n hn
specialize ha n
rewrite [ha]
have : ((3 : ℝ) * n + (-1) ^ n) / (2 * n + 5) - 3 / 2 =
  ((-1) ^ n * 2 - 15) / (2 * (2 * n + 5))
  := by field_simp; ring_nf
rewrite [this]
have : |((-1 : ℝ) ^ n * 2 - 15) / (2 * (2 * ↑n + 5))| =
  |((-1 : ℝ) ^ n * 2 - 15)|
   /
   |((2 : ℝ) * (2 * ↑n + 5))| := by apply abs_div
rewrite [this]
have h' : |(-1) ^ n * 2 - 15| ≤ 17 := by sorry -- bound FAILS
have : (N : ℝ) ≤ n := by exact_mod_cast hn
have : 0 < (2 : ℝ) * (2 * n + 5) := by bound
have : |(2 : ℝ) * (2 * n + 5)| = (2 : ℝ) * (2 * n + 5) := by apply abs_of_pos this
rewrite [this]
have hh : (2 : ℝ) * (2 * N) ≤ (2 : ℝ) * (2 * n + 5) := by bound
have hhh : 0 < (2 : ℝ) * (2 * N) := by nlinarith
have hh' : |(-1 : ℝ) ^ n * 2 - 15| / (2 * (2 * n + 5)) ≤
  17 / ((2 : ℝ) * (2 * N)) := by field_simp; sorry --bound --nlinarith
have : (17 : ℝ) / (2 * (2 * N)) < ε := by field_simp; bound
linarith [hh', this]

Conclusion "Done."
