import Game.Levels.L3Pset.L3Pset1

open Nat

World "L3Pset"
Level 4
Title "Problem 4"

Introduction "# Problem 4"

lemma ArchimedeanProp {ε : ℝ} (hε : 0 < ε) :
  ∃ N : ℕ, 1 / ε < N := by
  use ⌈1/ε⌉₊ + 1
  have : 1 / ε ≤ ⌈1/ε⌉₊ := by apply le_ceil
  push_cast
  linarith [this]


example (x y : ℝ) (x_pos : 0 < x) (y_pos : 0 < y) : ∃ N : ℕ, y < x * N := by
  use ⌈y / x⌉₊ + 1
  have : y / x ≤ ⌈ y / x ⌉₊ := by apply le_ceil
  have : y ≤ x * ⌈ y / x ⌉₊ := by exact (div_le_iff₀' x_pos).mp this
-- rw [← mul_lt_mul_left cpos] at h
  push_cast
--  ring_nf
  linarith [this, x_pos]



/-- Prove that the product of two convergent sequences converges to the product of their limits. -/
Statement (a : ℕ → ℝ) (ha : ∀ n, a n = 1 / n) : SeqLim a 0 := by
  change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - 0| < ε
  intro ε hε
  have : ∃ N : ℕ, 1 / ε < N := by apply ArchimedeanProp hε
  choose N hN using this
  use N
  intro n hn
  specialize ha n
  rewrite [ha]
  ring_nf
  have : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have : |(n : ℝ)⁻¹| = (n : ℝ)⁻¹ := by apply abs_of_nonneg  this
  rewrite [this]
  have : (N : ℝ) ≤ n := by exact_mod_cast hn

  sorry


Conclusion "Done."
