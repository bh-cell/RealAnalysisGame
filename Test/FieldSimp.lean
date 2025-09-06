import Game.Metadata

example (c : ℝ) (hc : c ≠ 0) (cpos : 0 < |c|) (cinvpos : 0 < |c|⁻¹)
    (a : ℝ) (ε : ℝ) (hε : 0 < ε) (h : |a| < ε * |c|⁻¹) : |c| * |a| < ε := by
  field_simp at h
  rw [mul_comm]
  assumption
