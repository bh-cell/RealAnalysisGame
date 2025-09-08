import Game.Levels.L2Pset.L2Pset1

World "L3Pset"
Level 3
Title "Problem 3"

Introduction "# Problem 3"

def IsBddBy (a : ℕ → ℝ) (M : ℝ) : Prop := ∀ n, |a n| ≤ M

def IsBdd (a : ℕ → ℝ) : Prop := ∃ M, IsBddBy a M

/-- Prove that the product of two convergent sequences converges to the product of their limits. -/
Statement (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) : IsBdd a := by
  change ∃ M, ∀ n, |a n| ≤ M
  change ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε at ha

  -- Get N such that |a n - L| < 1 for n ≥ N
  obtain ⟨N, hN⟩ := ha 1 (by norm_num : (1 : ℝ) > 0)

  -- Define M as the maximum of |L| + 1 and the maximum of |a i| for i < N
  let finite_max : ℝ := sorry --Finset.sup (Finset.range N) (fun i => |a i|₊)
  use max (|L| + 1) finite_max

  -- intro n
  -- -- Case split: n < N or n ≥ N
  -- by_cases h : n < N
  -- · -- Case: n < N
  --   apply le_max_of_le_right
  --   exact Finset.le_sup'_of_le (Finset.mem_range.mpr h) le_rfl

  -- · -- Case: n ≥ N
  --   push_neg at h
  --   -- Use triangle inequality: |a n| ≤ |a n - L| + |L|
  --   calc |a n|
  --     = |(a n - L) + L|         := by ring_nf
  --     _ ≤ |a n - L| + |L|       := abs_add _ _
  --     _ < 1 + |L|               := by linarith [hN n h]
  --     _ = |L| + 1               := by ring
  --     _ ≤ max (|L| + 1) finite_max := le_max_left _ _

  sorry

Conclusion "Done."
