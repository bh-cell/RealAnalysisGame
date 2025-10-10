import Game.Levels.L10Levels.L07_Order

open Finset

World "Lecture10"
Level 3
Title "Subsequences"



Introduction "
# Level 3: Subsequence Theorem

definition: `Subseq`

A sequence `σ : ℕ → ℕ` is a *subsequence* if it's strictly increasing: `∀ i j, i < j → σ (i) < σ (j)`

(Saw this in Problem 4 of Lecture 8 Pset.)
"

/-- A sequence `σ : ℕ → ℕ` is a *subsequence* if `∀ i j, i < j → σ (i) < σ (j)`. -/
DefinitionDoc Subseq as "Subseq"

NewDefinition Subseq

def Subseq (σ : ℕ → ℕ) : Prop :=
  ∀ i j, i < j → σ i < σ j

/--
If a sequence `a` converges to `L` and `σ` is a subsequence, then `a ∘ σ` also converges to `L`.
-/
TheoremDoc SubseqConv as "SubseqConv" in "Theorems"

/-- Prove this
-/
Statement SubseqConv (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) (σ : ℕ → ℕ) (hσ : Subseq σ) :
    SeqLim (a ∘ σ) L := by
intro ε hε
choose N hN using ha ε hε
use N
intro n hn
have f1 : n ≤ σ n := by apply SubseqGe hσ n
have f2 : N ≤ σ n := by linarith [f1, hn]
specialize hN (σ n) f2
apply hN

Conclusion ""

-- OrderLimGe in exercises
