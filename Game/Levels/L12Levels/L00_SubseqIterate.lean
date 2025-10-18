import Game.Levels.L11Lecture

World "Lecture12"
Level 1
Title "Iterated Subsequence"


Introduction "
# Level 1: Iterated Subsequence

Let's warm up to the topics of this lecture with a little exercise.

Suppose you have a sequence of *natural* numbers, `σ : ℕ → ℕ`,
and all you know about it is that it always exceeds the identity,

`hσ : ∀ n, n < σ n`

Now, this of course doesn't mean that `σ n` is itself strictly increasing (what we call a `Subseq`), the sequence could jump around all over the place, as long as its graph stays above that of $y=x$.

But hopefully it's \"intuitively clear\" from `hσ` that `σ` eventually blows up, gets larger and larger over time, just not monotonically so; that is, there should be *some* way to \"accelerate\" `σ` so that it
becomes a `Subseq`. The only problem is: how do you *actually* do this?

The key idea is that of an **orbit**. In astronomy, you can imagine looking up at the sky
night after night and trying to track the location of, say, Jupiter against the \"fixed\" stars (celestial sphere). You start your observations with Jupiter having some \"phase-space\" (position,velocity)
$x_0$; let $T$ be the function that runs Newtonian dynamics for one day, so that $T(x_0)$ is the new phase-space of Jupiter tomorrow, moving as it does according to Newton's laws and gravity. Then $T(T(x_0))$ is the phase space after two days, and so on. The whole
**orbit** of Jupiter over time is then the sequence: $x_0, T(x_0), T(T(x_0)), T(T(T(x_0))),\\dots$.

More generally, if you have any function $f : X \\to X$ that takes an abstract space  $X$ to itself,
and you start with some base point $x_0 : X$, then we will write $f^{[n]}(x_0)$ for $f$ iterated $n$ times applied to $x_0$. The sequence $n \\mapsto f^{[n]}(x_0)$ is called the \"orbit of $x_0$ under
the action of $f$\".

How does that help us in our present situation? We could start with any base point `n₀ : ℕ`, and we know from `hσ` specialized to `n = n₀` that `n₀ < σ n₀`,
but we have no idea how big `σ n₀` is; it could be huge. So how do we ensure that the next term exceeds `σ n₀`? (Want to think about it for a minute before reading on?)

Given our previous discussion, hopefully you see right away that: if we were to specialize `hσ` to `n = σ n₀`, we
would get: `σ n₀ < σ (σ n₀)`. So now it's clear: the way to get larger and larger terms from the sequence `σ`
is to take the orbit!

With these hints, your goal in this level is to prove the following

Theorem: for any fixed `n₀`, the orbit `n ↦ σ^[n] n₀` is a `Subseq`.

## New theorems:

- `succ_iterate`

While `σ^[k] (σ n) = σ^[k+1] (n)` is true by definition, it takes
an argument by induction to show that if instead of adding a `σ` on the right, we add it on the left: `σ (σ^[k] n) = σ^[k+1] n`. I'll spare you the proof of that argument, and give you the theorem `succ_iterate`.

- `subseq_of_succ`

To prove that `σ` is a `Subseq`, the definition of which speaks of all `i < j`, it's enough to
do it one step at a time. The theorem `subseq_of_succ` says that
it's enough to show that `σ n < σ (n+1)` holds for all `n` to conclude `Subseq σ`.
You can `apply` this fact to reduce showing `Subseq σ` to just showing it for going from `n` to `n+1`.

## New tactic: `show` Syntax: `show fact by proof`, for example, if
you want to rewrite by the fact that `σ (σ^[n] n₀) = σ^[n+1] n₀` without
a separate `have` declaration, you can write:

`rewrite [show σ (σ^[n] n₀) = σ^[n+1] n₀ by apply succ_iterate]`

"

/-- The `show` tactic has syntax `show fact by proof`. -/
TacticDoc «show»

NewTactic «show»

theorem succ_iterate (σ : ℕ → ℕ) (k : ℕ) (n : ℕ) :
σ (σ^[k] n) = σ^[k+1] n :=
Eq.symm (Function.iterate_succ_apply' σ k n)

/-- For a function `σ : ℕ → ℕ`, we have that: `σ (σ^[k]) = σ^[k+1]`. -/
TheoremDoc succ_iterate as "succ_iterate" in "Theorems"


theorem subseq_of_succ (σ : ℕ → ℕ) (hσ : ∀ n, σ n < σ (n + 1)) : Subseq σ := by
  intro i j hij
  induction hij with
  | refl => exact hσ i
  | step hi h =>
      specialize hσ m
      linarith [h, hσ]

/-- For a function `σ : ℕ → ℕ`, if `σ n < σ (n+1)`, then
for any `i < j`, `σ i < σ j` -- that is, `Subseq σ` holds. -/
TheoremDoc subseq_of_succ as "subseq_of_succ" in "Theorems"

NewTheorem subseq_of_succ succ_iterate


/--
If a sequence `σ : ℕ → ℕ` grows faster than the identity, `n < σ n`,
then the orbit of any base point `n₀ : ℕ` under `σ` -- this means the sequence `n₀, σ n₀, σ^[2] n₀, ...` -- is a `Subseq`, that is, is strictly increasing.
-/
TheoremDoc Subseq_of_Iterate as "Subseq_of_Iterate" in "Theorems"

/-- Prove this
-/
Statement Subseq_of_Iterate (σ : ℕ → ℕ) (hσ : ∀ n, n < σ n) (n₀ : ℕ) :
  Subseq (fun n ↦ σ^[n] n₀) := by
  apply subseq_of_succ
  intro n
  specialize hσ (σ^[n] n₀)
  have f : σ (σ^[n] n₀) = σ^[n+1] n₀ := by apply succ_iterate
  rewrite [f] at hσ
  apply hσ

Conclusion "
"
