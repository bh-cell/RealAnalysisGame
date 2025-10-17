import Game.Levels.L12Levels.L00_IterateGap

World "Lecture12"
Level 2
Title "Monotone and Bounded Implies Cauchy"


Introduction "
# Level 2: Monotone and Bounded Implies Cauchy

## New tactic: `push_neg`

The negation of `∀` is `∃`, and vice-versa. To push a chain of negations through, write `push_neg`.

"

/-- The `push_neg` tactic pushes negations through universal and existential quantifiers, inequalities, etc. -/
TacticDoc push_neg

NewTactic push_neg

/--
If a sequence `a : ℕ → X` (where `X` can be `ℚ` or `ℝ`) is monotone and bounded, then it is Cauchy.
-/
TheoremDoc IsCauchyOfMonotoneBdd as "IsCauchyOfMonotoneBdd" in "Theorems"

/-- Prove this
-/
Statement IsCauchyOfMonotoneBdd {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] [FloorSemiring X] (a : ℕ → X) (M : X) (hM : ∀ n, a n ≤ M) (ha : Monotone a)
    : IsCauchy a := by
intro ε hε
by_contra h
push_neg at h
choose τ hτ σ hσ hgap using h
have f1 : ∀ k, k * ε ≤ a (σ^[k] 0) - a 0 := by apply IterateGap a ha ε hε τ hτ σ hσ hgap
let k : ℕ := ⌈(M - a 0) / ε⌉₊ + 1
have hk' : (M - a 0) / ε ≤  ⌈(M - a 0) / ε⌉₊ := by bound
have hk : (M - a 0) / ε < k := by change (M - a 0) / ε < (⌈(M - a 0) / ε⌉₊ + 1 : ℕ); push_cast; linarith [hk']
specialize f1 k
specialize hM (σ^[k] 0)
have f2 : (M - a 0) < k * ε := by field_simp at hk; rewrite [show k * ε = ε * k by ring_nf]; apply hk
linarith [f1, f2, hM]

Conclusion ""
