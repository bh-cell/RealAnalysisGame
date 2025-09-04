import Game.Levels.L2Pset.L2Pset1

World "L2Pset"
Level 2
Title "Problem 2"

Introduction "# Problem 2"

/-- For two sequences `a b : ℕ → ℝ` and real numbers `L M : ℝ`, with the hypotheses that `SeqLim a L` and `SeqLim b M`, the theorem `ProdLim` says that if
there is a third sequence `c : ℕ → ℝ` so that for all `n`, `c n = a n * b n` (that is, `c` is the product of the sequences), then `SeqLim c (L * M)` holds. -/
TheoremDoc ProdLim as "ProdLim" in "Theorems"

/-- Prove that the product of two convergent sequences converges to the product of their limits. -/
Statement ProdLim (a b c : ℕ → ℝ) (L M : ℝ)
    (ha : SeqLim a L) (hb : SeqLim b M) (hc : ∀ n, c n = a n * b n) :
    SeqLim c (L * M) := by
  change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |c n - (L * M)| < ε
  intro ε hε
  unfold SeqLim at ha hb
  change ∀ ε₁ > 0, ∃ Na : ℕ, ∀ n ≥ Na, |a n - L| < ε₁ at ha
  change ∀ ε₂ > 0, ∃ Nb : ℕ, ∀ n ≥ Nb, |b n - M| < ε₂ at hb

  -- First, get boundedness of sequence a
  specialize ha 1
  have one_pos : (0 : ℝ) < 1 := by norm_num
  specialize ha one_pos
  choose Na₁ hNa₁ using ha
  -- For simplicity, let's use K = |L| + 1 and handle the finitely many initial terms separately

  -- Choose appropriate epsilons for the two factors
  have eps_pos : 0 < ε / (2 * (|L| + |M| + 1)) := by
    positivity


--   choose Na hNa using ha
--   choose Nb hNb using hb
--   use Na + Nb + Na₁

--   intro n hn
--   specialize hc n
--   rewrite [hc]

--   -- Key algebraic manipulation: a(n)*b(n) - L*M = a(n)*(b(n) - M) + M*(a(n) - L)
--   have key_identity : a n * b n - L * M = a n * (b n - M) + M * (a n - L) := by ring
--   rewrite [key_identity]

--   -- Apply triangle inequality
--   have triangle : |a n * (b n - M) + M * (a n - L)| ≤ |a n * (b n - M)| + |M * (a n - L)| :=
--     by exact abs_add _ _

--   -- Use |a*b| = |a|*|b| property
--   have prod_abs₁ : |a n * (b n - M)| = |a n| * |b n - M| := abs_mul _ _
--   have prod_abs₂ : |M * (a n - L)| = |M| * |a n - L| := abs_mul _ _

--   -- Get bounds on |a n|
--   have ineq_a : Na ≤ n := by linarith [hn]
--   have ineq_b : Nb ≤ n := by linarith [hn]
--   have ineq_bound : Na₁ ≤ n := by linarith [hn]

--   specialize hNa n ineq_a
--   specialize hNb n ineq_b
--   specialize hNa₁ n ineq_bound

--   -- Since |a n - L| < 1, we have |a n| ≤ |L| + 1
--   have bound_a : |a n| ≤ |L| + 1 := by
--     have : |a n| = |(a n - L) + L| := by ring_nf
--     rw [this]
--     exact le_trans (abs_add _ _) (by linarith [hNa₁])

--   -- Combine everything
--   calc |a n * (b n - M) + M * (a n - L)|
--     ≤ |a n * (b n - M)| + |M * (a n - L)| := triangle
--     _ = |a n| * |b n - M| + |M| * |a n - L| := by rw [prod_abs₁, prod_abs₂]
--     _ ≤ (|L| + 1) * |b n - M| + |M| * |a n - L| := by linarith [bound_a]
--     _ < (|L| + 1) * (ε / (2 * (|L| + |M| + 1))) + |M| * (ε / (2 * (|L| + |M| + 1))) := by linarith [hNa, hNb]
--     _ = ε * (|L| + 1 + |M|) / (2 * (|L| + |M| + 1)) := by ring
--     _ ≤ ε / 2 + ε / 2 := by linarith
--     _ = ε := by ring
  sorry

Conclusion "Done."
