import Game.Levels.L10Pset.L10Pset5

World "L10Pset"
Level 5
Title "Problem 5"

Introduction "
# Problem 5:

Show that the sequence `a n = n` is unbounded.

"

/-- Prove this
-/
Statement (a : ℕ → ℝ) (ha : ∀ n, a n = n) : ¬ SeqBdd a := by
intro h
choose L Lpos hL using h
let N : ℕ := ⌈L⌉₊ + 1
have hN : (N : ℝ) = ⌈L⌉₊ + 1 := by norm_cast
have hL' : L ≤ ⌈L⌉₊ := by bound
have hNL : L < N := by linarith [hL', hN]
specialize hL N
rewrite [ha] at hL
have Npos : (0 : ℝ) ≤ N := by norm_cast; bound
rewrite [(by apply abs_of_nonneg Npos : |(N : ℝ)| = N)] at hL
linarith [hL, hNL]

Conclusion "Done."
