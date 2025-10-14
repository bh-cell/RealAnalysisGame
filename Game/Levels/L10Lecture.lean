import Game.Levels.L10Levels.L06_Prod
import Game.Levels.L10Levels.L07_Order
import Game.Levels.L10Levels.L08_Mono
import Game.Levels.L10Levels.L09_Subseq

World "Lecture10"
Title "Lecture 10: Algebraic Limit Theorem, Part V"


Introduction "
# Lecture 10: Algebraic Limit Theorem, Part V

Welcome to Lecture 10! We're completing the foundation of sequence theory by tackling three major topics:

## 1. Products of Sequences (The Big Boss!)

We finish the **Algebraic Limit Theorem** by proving that products of convergent sequences converge:
- If `a n → L` and `b n → M`, then `a n * b n → L * M`

This is the hardest part of the Algebraic Limit Theorem, requiring a clever trick. The geometric intuition comes from thinking about rectangles and the product rule from calculus.

Combined with our earlier work, you'll be able to compute limits of any algebraic expression!

## 2. Order Limit Theorem

Next, we shift from algebra to **inequalities**. Does boundedness pass through limits?
- If `a n ≤ K` for all `n` and `a n → L`, then `L ≤ K`

This theorem respects the order structure of the real numbers and is fundamental for comparison arguments. We'll prove it by contradiction—a beautiful example of when that technique is the natural choice.

**Warning:** Strict inequalities don't pass through! Even if `a n < K` for all `n`, we only get `L ≤ K`.

## 3. Subsequences

Finally, we introduce **subsequences**—sequences formed by dropping out some terms and sliding everyone to the left.

The key result: **every subsequence of a convergent sequence converges to the same limit**.

The contrapositive gives us a powerful divergence test: if two subsequences converge to different limits, the original sequence diverges!

We'll see this in action with `a n = (-1)^n`, which oscillates but has subsequences converging to 1 (even indices) and -1 (odd indices).

---

**What You'll Learn:**

By the end of this lecture, you'll have:
- ✅ The complete **Algebraic Limit Theorem** (sums, products, quotients, scalar multiples)
- ✅ Tools for working with **inequalities and limits**
- ✅ The **Subsequence Theorem** and how to use it to prove divergence
- ✅ New proof techniques: geometric thinking for products, contradiction for orders

Let's dive in!
"
