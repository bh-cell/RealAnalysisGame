import Game.Levels.L9Levels.L05_BddOfConv

open Finset

World "Lecture9"
Level 3
Title "Big Boss : Product of Sequences"



Introduction "
# Level 3: Big Boss

Good luck!

"
/--
`ProdLim`
-/
TheoremDoc ProdLim as "ProdLim" in "Theorems"

/-- Prove this
-/
Statement ProdLim (a b c : ℕ → ℝ) (L M : ℝ) (hL : L ≠ 0) (hM : M ≠ 0) (ha : SeqLim a L)
    (hb : SeqLim b M) (hc : ∀ n, c n = a n * b n):
    SeqLim c (L * M) := by
intro ε hε
choose K hK using BddOfConvNonzero b M hb hM
have ε1 : 0 < ε / (2 * K) := by bound
have absL : 0 < |L| := by apply abs_pos_of_nonzero hL
have ε2 : 0 < ε / (2 * |L|) := by bound
specialize ha (ε / (2 * K)) ε1
specialize hb (ε / (2 * |L|)) ε2
choose N1 hN1 using ha
choose N2 hN2 using hb
use N1 + N2
intro n hn
have hn1 : N1 ≤ n := by bound
have hn2 : N2 ≤ n := by bound
specialize hN1 n hn1
specialize hN2 n hn2
specialize hc n
rewrite [hc]
have f1 : |a n * b n - L * M| = |(a n - L) * b n + (L * (b n -  M))| := by ring_nf
have f2 : |(a n - L) * b n + (L * (b n -  M))| ≤ |(a n - L) * b n| + |(L * (b n -  M))| := by apply abs_add
have f3 : |(a n - L) * b n| = |(a n - L)| * |b n| := by apply abs_mul
have bnBnd : |b n| ≤ K := by apply hK.2 n
have f5 : |(a n - L)| * |b n| ≤ ε / (2 * K) * K := by bound
have Kpos : 0 < K := by apply hK.1
have f6 : ε / (2 * K) * K = ε / 2 := by field_simp
have f7 : |(L * (b n -  M))| = |L| * |b n -  M| := by apply abs_mul
have f8 :  |L| * |b n -  M| < |L| * (ε / (2 * |L|)) := by bound
have f9 : |L| * (ε / (2 * |L|)) = ε / 2 := by field_simp
linarith [f1, f2, f3, f5, f6, f7, f8, f9]

Conclusion ""

-- case `L = 0` in exercises
-- general case in exercises!
