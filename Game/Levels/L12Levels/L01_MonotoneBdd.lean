import Game.Levels.L12Levels.L00_SubseqIterate

World "Lecture12"
Level 2
Title "Monotone and Bounded Implies Cauchy"


Introduction "
# Level 2: Monotone and Bounded Implies Cauchy

## New definition: `Monotone`

## New theorem: `Monotone_of_succ`

To prove monotonicity, it is enough to prove it one step at a time; that is, if `a m ≤ a (m+1)` holds for all `m`, then `a` is `Monotone`.

## New tactic: `push_neg`

The negation of `∀` is `∃`, and vice-versa. To push a chain of negations through, write `push_neg`.

## Postponed to next level:

Once we get our hands on some `ε` amount of growth, iterate it to get `k * ε` growth, for any `k`.

Theorem `IterateGap` : Given `(a : ℕ → X) (ha : Monotone a) (ε : X) (εpos : ε > 0) (τ : ℕ → ℕ)
    (hτ : ∀ n, τ n ≥ n) (σ : ℕ → ℕ) (hσ : ∀ n, σ n ≥ τ n) (hgap : ∀ n, ε ≤ |a (σ n) - a (τ n)|)
    : ∀ k, k * ε ≤ a (σ^[k] 0) - a 0

"

/-- `(a : X → Y) {i j} (hij : i ≤ j) : a i ≤ a j`

A sequence `a : X → Y` is said to be `Monotone` if `a n ≤ a m` whenever `n ≤ m`. -/
DefinitionDoc Monotone as "Monotone"

NewDefinition Monotone

theorem Monotone_of_succ {X : Type*} [Preorder X] (a : ℕ → X) (ha : ∀ n, a n ≤ a (n + 1)) : Monotone a := by
exact monotone_nat_of_le_succ ha

/-- If `a n ≤ a (n+1)` holds for all `n`, then `a` is `Monotone`. -/
TheoremDoc Monotone_of_succ as "Monotone_of_succ" in "Theorems"

theorem IterateGap {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] (a : ℕ → X) (ha : Monotone a) (ε : X)
  (εpos : ε > 0)
  (τ : ℕ → ℕ) (hτ : ∀ n, τ n ≥ n)
  (σ : ℕ → ℕ) (hσ : ∀ n, σ n ≥ τ n)
  (hgap : ∀ n, ε ≤ |a (σ n) - a (τ n)|)
  : ∀ (k : ℕ), k * ε ≤ a (σ^[k] 0) - a 0
  := by
intro k
induction' k with k hk
norm_num
specialize hgap (σ^[k] 0)
rewrite [(show |a (σ (σ^[k] 0)) - a (τ (σ^[k] 0))| = a (σ (σ^[k] 0)) - a (τ (σ^[k] 0)) by apply abs_of_nonneg (by bound))] at hgap
rewrite [show σ (σ^[k] 0) = σ^[k + 1] 0 by apply succ_iterate] at hgap
have f1 : 0 ≤ a (τ (σ^[k] 0)) - a (σ^[k] 0) := by bound
push_cast
linarith [f1, hk, hgap]


/--
If a sequence `a : ℕ → X` (where `X` could be `ℚ` or `ℝ`) is `Monotone` and grows along some subsequences by `ε`, then it eventually grows by `k * ε` for any `k`.
-/
TheoremDoc IterateGap as "IterateGap" in "Theorems"

NewTheorem Monotone_of_succ IterateGap

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
