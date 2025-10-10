import Game.Levels.L10Levels.L06_Prod

open Finset

World "Lecture10"
Level 2
Title "Order Limit Theorem"

Introduction "
# Level 2: Order Limit Theorem

"
/--
If a sequence `a` converges to `L` and `a n ≤ K` for all `n`, then `L ≤ K`.
-/
TheoremDoc OrderLimLe as "OrderLimLe" in "Theorems"

/-- Prove this
-/
Statement OrderLimLe (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) (K : ℝ) (hK : ∀ n, a n ≤ K) :
    L ≤ K := by
by_contra hL
have hL' : K < L := by bound
have hLK : 0 < (L - K) / 2 := by linarith [hL']
choose N hN using ha ((L - K) / 2) hLK
specialize hN N (by bound)
rewrite [abs_lt] at hN
have f1 : L - ((L - K) / 2) < a N := by linarith [hN.1]
have f2 : K ≤ L - ((L - K) / 2) := by linarith [hL']
specialize hK N
linarith [f2, hK, f1]

Conclusion ""

-- OrderLimGe in exercises
