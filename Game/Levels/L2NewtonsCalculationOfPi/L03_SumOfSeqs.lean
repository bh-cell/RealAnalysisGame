import Game.Levels.L2NewtonsCalculationOfPi.L02_DoubleSeqConv

World "NewtonsCalculationOfPi"
Level 3
Title "Big Boss: The Sum of Convergent Sequences"

Introduction "
# Lecture 2 **Big Boss**: Adding Convergent Sequences

Now that we've had some experience with the definition of convergence, let's tackle this world's Big Boss. One of the most fundamental ideas in analysis is that 'nice operations preserve convergence.' If two sequences each converge, then their sum also converges, and converges to the sum of their limits.

This might seem obvious at first -- after all, if $a_1(n)$ is getting close to $L_1$ and $a_2(n)$ is getting close to $L_2$, shouldn't $a_1(n) + a_2(n)$ get close to $L_1 + L_2$? While the intuition is correct, making this rigorous requires some clever maneuvering with our epsilon-N definition.

**Lecture 2 Big Boss**
Here's the key insight: if an engineer demands that our combined output be within $\\varepsilon$ of the target $L_1 + L_2$, we can't just demand that each factory independently meet the full tolerance $\\varepsilon$. Instead, we need to be clever about how we allocate our 'tolerance budget.'

Think of it this way: if the first factory can guarantee its output is within $\\varepsilon/2$ of $L_1$, and the second factory can guarantee its output is within $\\varepsilon/2$ of $L_2$, then by the triangle inequality, their sum will be within $\\varepsilon$ of $L_1 + L_2$. This is the heart of the proof!

## The Mathematical Setup

Suppose we have:
- A sequence $a_1 : \\mathbb{N} \\to \\mathbb{R}$ that converges to $L_1$
- A sequence $a_2 : \\mathbb{N} \\to \\mathbb{R}$ that converges to $L_2$
- A sequence $a : \\mathbb{N} \\to \\mathbb{R}$ with the property that $a(n) = a_1(n) + a_2(n)$ for all $n$

We want to prove that $a$ converges to $L_1 + L_2$.

## New Tool

You'll only need one new theorem:

**The triangle inequality**: The theorem `abs_add` states that `|x + y| ≤ |x| + |y|` for any real numbers `x` and `y`. This is crucial for our tolerance-splitting strategy.
Again, when `x` and `y` are complicated expressions, the same Lean time-saving trick applies here; you can write:

`have NewInequality : |SomethingLongAndComplicated + SomethingElse| ≤
|SomethingLongAndComplicated| + |SomethingElse| :=
by exact abs_add _ _`

and Lean will figure out what the underscores are supposed to be.

## Your Strategic Approach

- Start by unfolding the definitions of `SeqLim` in the Goal and hypotheses. I recommend you give your dummy variables different names, so as not to get confused later.
- Given any `ε > 0`, use the convergence of `a₁` to get an `N₁` that works for `ε / 2`.
- Similarly, use the convergence of `a₂` to get an `N₂` that works for `ε / 2`
- You might think that it would be a good idea at this point to `use max N₁ N₂`, that is, take the larger of the two for `N`. But we don't care how big `N` is! Can you
think of another way to achieve the same objective? (Hint:
 I haven't told you how to use the `max` function, but you
 already have everything you need at your disposal...)
- Use the triangle inequality to combine the two half-tolerances

This proof embodies a fundamental principle in analysis: when dealing with sums, we often need to 'divide and conquer' by splitting our error tolerance between the components.
"

/-- For any real numbers `x` and `y`, we have `|x + y| ≤ |x| + |y|`. -/
TheoremDoc abs_add as "abs_add" in "Theorems"

NewTheorem abs_add

/-- For two sequences `a₁ a₂ : ℕ → ℝ` and real numbers `L₁ L₂ : ℝ`, with the hypotheses that `SeqLim a₁ L₁` and `SeqLim a₂ L₂`, the theorem `SumLim` says that if
there is a third sequence `a : ℕ → ℝ` so that for all `n`, `a n = a₁ n + a₂ n` (that is, `a` is the sum of the sequences), then `SeqLim a (L₁ + L₂)` holds. -/
TheoremDoc SumLim as "SumLim" in "Theorems"

/-- Prove that the sum of two convergent sequences converges to the sum of their limits.
This is the mathematician's version of 'if two factories each meet their quality standards, their combined output will too!' -/
Statement SumLim (a₁ a₂ a : ℕ → ℝ) (L₁ L₂ : ℝ)
    (h₁ : SeqLim a₁ L₁) (h₂ : SeqLim a₂ L₂) (a_sum : ∀ n, a n = a₁ n + a₂ n) :
    SeqLim a (L₁ + L₂) := by
  change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - (L₁ + L₂)| < ε
  intro ε hε
  unfold SeqLim at h₁
  change ∀ ε₁ > 0, ∃ N₁ : ℕ, ∀ n ≥ N₁, |a₁ n - L₁| < ε₁ at h₁
  change ∀ ε₂ > 0, ∃ N₂ : ℕ, ∀ n ≥ N₂, |a₂ n - L₂| < ε₂ at h₂
  specialize h₁ (ε / 2)
  specialize h₂ (ε / 2)
  have eps_on_2_pos : 0 < ε / 2 := by linarith [hε]
  specialize h₁ eps_on_2_pos
  specialize h₂ eps_on_2_pos
  choose N₁ hN₁ using h₁
  choose N₂ hN₂ using h₂
  use N₁ + N₂
  intro n hn
  specialize a_sum n
  rewrite [a_sum]
  have thing : a₁ n + a₂ n - (L₁ + L₂) =
    (a₁ n - L₁) + (a₂ n - L₂) := by ring_nf
  rewrite [thing]
  specialize hN₁ n
  specialize hN₂ n
  have ineq₁ : N₁ ≤ n := by linarith [hn]
  have ineq₂ : N₂ ≤ n := by linarith [hn]
  specialize hN₁ ineq₁
  specialize hN₂ ineq₂
  have ineq₃ : |a₁ n - L₁ + (a₂ n - L₂)| ≤
    |a₁ n - L₁| + |(a₂ n - L₂)| := by exact abs_add _ _
  linarith only [hN₁, hN₂, ineq₃]


Conclusion "
# 🎉 Outstanding! 🎉

You've just proven one of the fundamental theorems of analysis! Let's celebrate what you accomplished and understand why this result is so powerful.

**Why This Matters:**
This theorem and others like it are the foundation for all of calculus! Every time we differentiate or integrate a sum, we're implicitly using arguments of this kind.

**The Deeper Insight:**
Notice how the proof required more than just intuition. The 'obvious' fact that sums of convergent sequences converge needed careful epsilon management. This is the hallmark of rigorous analysis: making intuitive ideas completely precise.

## Check in, in Natural Language

Yet again, let's step back from the formal Lean proof and understand what we just proved in plain English.

**Theorem (in natural language):** If two sequences of real numbers converge to their respective limits, then the sequence formed by adding corresponding terms also converges, and its limit is the sum of the original limits.

**Proof:** Suppose sequences $a_1(n)$ and $a_2(n)$ converge to $L_1$ and $L_2$ respectively, and we want to show that $a(n) = a_1(n) + a_2(n)$ converges to $L_1 + L_2$.

By definition, we need to show that for any tolerance $\\varepsilon > 0$, we can find a point $N$ such that for all $n \\geq N$, we have $|a(n) - (L_1 + L_2)| < \\varepsilon$.

Since $a_1(n)$ converges to $L_1$, we can find $N_1$ such that $|a_1(n) - L_1| < \\varepsilon/2$ for all $n \\geq N_1$.
Since $a_2(n)$ converges to $L_2$, we can find $N_2$ such that $|a_2(n) - L_2| < \\varepsilon/2$ for all $n \\geq N_2$.

Let $N = N_1 + N_2$ (any number that's at least as large as both $N_1$ and $N_2$ would work). Then for any $n \\geq N$:

$$|a(n) - (L_1 + L_2)| = |(a_1(n) + a_2(n)) - (L_1 + L_2)| = |(a_1(n) - L_1) + (a_2(n) - L_2)|$$

By the triangle inequality, this is at most:
$$|a_1(n) - L_1| + |a_2(n) - L_2| < \\frac{\\varepsilon}{2} + \\frac{\\varepsilon}{2} = \\varepsilon$$

Therefore, $a(n)$ converges to $L_1 + L_2$. **QED**

"
