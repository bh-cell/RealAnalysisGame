import Game.Levels.L3Pset.L3Pset3

open Nat

World "L3Pset"
Level 4
Title "Problem 4"

Introduction "# Problem 4"


/-- Prove that the product of two convergent sequences converges to the product of their limits. -/
Statement (x y : ℝ) (x_pos : 0 < x) (y_pos : 0 < y) : ∃ N : ℕ, y < x * N  := by
  use ⌈y / x⌉₊ + 1
  have : y / x ≤ ⌈ y / x ⌉₊ := by bound
  field_simp at this
  push_cast
--  ring_nf
  linarith [this, x_pos]


Conclusion "Done."
