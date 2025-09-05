import Game.Levels.L2NewtonsCalculationOfPi
import Game.CustomTactic.Linarith

World "L2Pset"
Level 1
Title "Problem 1"

Introduction "# Problem 1"

/-- Prove that if `c` is a nonzero constant and `lim a = L`, and `b (n) = c * a (n)` for all `n`, then `lim b = c * L`. -/
Statement (c : ℝ) (hc : c ≠ 0) (a : ℕ → ℝ) (L : ℝ)
    (ha : SeqLim a L) (b : ℕ → ℝ)
    (hb : ∀ n, b n = c * a n) :
    SeqLim b (c * L) := by
change ∀ ε > 0, ∃ N, ∀ n ≥ N, |b n - c * L| < ε
intro ε hε
have thing : 0 < ε * |c|⁻¹ := by positivity
specialize ha (ε * |c|⁻¹) thing
choose N hN using ha
use N
intro n hn
specialize hb n
rewrite [hb]
have : c * a n - c * L = c * (a n - L) := by ring_nf
rewrite [this]
have : |c * (a n - L)| = |c| * |(a n - L)| := by apply abs_mul
rewrite [this]
specialize hN n hn
refine (lt_div_iff₀' ?_).mp hN
positivity


Conclusion "Done."
