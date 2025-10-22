import Game.Levels.L12Lecture

World "L12Pset"
Level 1
Title "Problem 1"

Introduction "
# Problem 1:

In lecture, we proved `IsCauchyOfMonotoneBdd`: if a sequence is `Monotone` and bounded (from above),
then it `IsCauchy`. Here you'll prove the same thing but going down: if a sequence is `Antitone` (that
is, non-increasing -- so decreasing but not necessarily strictly so; `i ≤ j → a j ≤ a i) and bounded
from *below*, then it's Cauchy.

Theorem: `IsCauchyOfAntitoneBdd`.

## New definition: `Antitone`

Hint: You don't need to reprove everything from scratch! I'll give you two tools:

## New theorems:

- `MonotoneNeg_of_Antitone`: if `a` is `Antitone`, then `-a` is `Monotone`.

- `IsCauchyNeg`: if `IsCauchy a`, then so is `IsCauchy (-a)`.

"

/-- `(a : X → Y) ∀ i j, i ≤ j → a j ≤ a i`

A sequence `a : X → Y` is said to be `Antitone` if `a m ≤ a n` whenever `n ≤ m` (note that `n` and `m` were reversed).
 -/
DefinitionDoc Antitone as "Antitone"

NewDefinition Antitone

theorem MonotoneNeg_of_Antitone {X : Type*} [LinearOrder X] [AddCommGroup X] [IsOrderedAddMonoid X]
(a : ℕ → X) (ha : Antitone a) : Monotone (-a) :=
fun i j hij ↦ neg_le_neg (ha hij)

/-- If `a` is `Antitone`, then `-a` is `Monotone`. -/
TheoremDoc MonotoneNeg_of_Antitone as "MonotoneNeg_of_Antitone" in "Theorems"

theorem IsCauchyNeg {X : Type*} [NormedField X] [Lattice X]
(a : ℕ → X) (ha : IsCauchy a) : IsCauchy (-a) := by
intro ε hε
choose N hN using ha ε hε
use N
intro n hn m hm
change |(- a m) - (- a n)| < ε
rewrite [show (- a m) - (- a n) = -(a m - a n) by ring_nf]
rewrite [show |-(a m - a n)| = |(a m - a n)| by apply abs_neg]
apply hN n hn m hm

/-- If `a` is `Antitone`, then `-a` is `Monotone`. -/
TheoremDoc IsCauchyNeg as "IsCauchyNeg" in "Theorems"


NewTheorem MonotoneNeg_of_Antitone IsCauchyNeg


/-- Prove `IsCauchyOfAntitoneBdd`
-/
Statement  {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] [FloorSemiring X] (a : ℕ → X) (M : X) (hM : ∀ n, M ≤ a n) (ha : Antitone a)
    : IsCauchy a := by
sorry

Conclusion ""
