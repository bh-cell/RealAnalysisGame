import Game.Levels.L5Levels.L01_Eventually
import Game.Levels.L5Levels.L02_SeqOfAbs
import Game.Levels.L5Levels.L03_SeqInvLim
import Game.Levels.L5Levels.L04_FiniteSums
import Game.Levels.L5Levels.L05_BddOfConv
import Game.Levels.L5Levels.L06_Prod


World "Lecture5"
Title "Lecture 5: Even more fun with Sequences"

Introduction "
# More on sequences


The so-called Algebraic Limit Theorem for sequences says that: if `a` and `b` are two sequences, `a b : ℕ → ℝ`, and `L` and `M` are two real numbers, with `lim a = L` and `lim b = M`, then:

- (i) for any constant `c`, `lim c * a = c * L` (you already proved this in the special case `c = 2`, and the general case is similar -- with one catch; can you tell what it is?)
- (ii) `lim (a + b) = L + M` (you already proved this as well)
- (iii) `lim (a * b) = L * M`, and
- (iv) `lim (a / b) = L / M`, as long as `M ≠ 0`.

Can you guess what the problem set is? :)
"
