import Game.Levels.L3Lecture

World "L3Pset"
Level 1
Title "Problem 1"

Introduction "# Problem 1"

/-- Prove the full Archimedean Property. -/
Statement (x y : ℝ) (x_pos : 0 < x) (y_pos : 0 < y) : ∃ N : ℕ, y < x * N  := by
  use ⌈y / x⌉₊ + 1
  have : y / x ≤ ⌈ y / x ⌉₊ := by bound
  field_simp at this
  push_cast
--  ring_nf
  linarith [this, x_pos]

Conclusion "Done."
