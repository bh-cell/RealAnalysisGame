import Game.Levels.L8Levels.L03_Induction'


World "Lecture8"
Title "Lecture 8: Induction"

Introduction "
# Lecture 8: Mathematical Induction

**SIMPLICIO:** Hey Socrates, I've been thinking about something that's been bothering me. When we prove things in mathematics, we usually prove a specific statement. But what if I want to prove something is true for *all* natural numbers? Like, how do I prove a statement for 0, 1, 2, 3, 4, and so on... forever?

**SOCRATES:** Ah, an excellent question! You're right that we can't just check each case one by one—that would take infinitely long. Tell me, Simplicio, have you ever climbed a ladder?

**SIMPLICIO:** Of course! What does that have to do with anything?

**SOCRATES:** Well, imagine an infinitely tall ladder reaching up to the sky. If I wanted to convince you that you *could* climb to any rung on this ladder, what would I need to show you?

**SIMPLICIO:** Hmm... I guess you'd need to show me that I can reach the bottom-most rung?

**SOCRATES:** Good start! And what else?

**SIMPLICIO:** Well, if I'm standing on any particular rung, I'd need to know I can reach the next one up. So if I can always step from one rung to the next...

**SOCRATES:** Exactly! So if you can reach the first rung, and you can always step from rung `k` to rung `k+1`, then what can you conclude?

**SIMPLICIO:** Oh! Then I can reach *any* rung I want! If I want to reach rung 100, I just start at rung 0, step to rung 1, then to rung 2, and keep going until I reach rung 100. And the same works for any number!

**SOCRATES:** Precisely! This is the essence of **mathematical induction**. To prove something is true for all natural numbers `n`, you need exactly two things:
- A **base case**: prove it's true for `n = 0`
- An **inductive step**: prove that *if* it's true for `n = k`, *then* it's true for `n = k + 1`

**SIMPLICIO:** Wait, but in the inductive step, aren't we assuming what we're trying to prove? Isn't that circular reasoning?

**SOCRATES:** An astute observation! But no, it's not circular. We're not assuming the statement is true for all `n`. We're only assuming it's true for one particular value `k`, and using that assumption to prove that it's true for `k + 1`. We're proving an implication: \"if `P(k)` then `P(k+1)`\". Combined with the base case, this creates a chain reaction that reaches any natural number.

**SIMPLICIO:** Hmm, I think I see. So the assumption \"it's true for `k`\" is called the inductive hypothesis?

**SOCRATES:** Exactly! And that hypothesis is your most powerful tool. It's like having a foothold on rung `k` that you can push off from to reach rung `k + 1`.

**SIMPLICIO:** But why does this work? I mean, why should I believe this principle?

**SOCRATES:** Ah, a deep question! It comes from the very definition of the natural numbers themselves. How do you think the natural numbers are constructed?

**SIMPLICIO:** Well... I guess we start with 0. And then we have 1, which is 0 + 1. And 2 is 1 + 1. So each number is the \"successor\" of the previous one?

**SOCRATES:** Beautiful! The natural numbers are defined by exactly this process:
- Zero is a natural number
- If `k` is a natural number, then `k + 1` is also a natural number
- These are the *only* natural numbers

Do you see how this mirrors the structure of induction?

**SIMPLICIO:** Oh wow! The base case corresponds to \"zero is a natural number,\" and the inductive step corresponds to \"if `k` is a natural number, then so is `k + 1`.\" Induction is just the construction of the natural numbers turned into a proof technique!

**SOCRATES:** Precisely! There are no \"gaps\" in the natural numbers—no number that can't be reached by starting at 0 and repeatedly adding 1. This is why induction works.

In fact, this is not just a philosophical observation—this is *literally* how the natural numbers are implemented in Lean! In Lean's type theory, a natural number is defined inductively as either:
- `zero : ℕ`, the base case, or
- `succ n : ℕ`, the successor of another natural number `n`

Here's how this looks in the core of Lean:

`inductive Nat where`
- `| zero : Nat`
- `| succ (n : Nat) : Nat`

You simply declare the existence of a natural number called `zero`, and then we declare that, given any natural number `n`, there's another one called `succ n`. (The word `succ` is here just a name for this constructor; we could have called it `Alice` instead. The important thing is that we're giving a way to construct a new natural number from a previously existing one.)

So the number 3, for instance, is literally represented as `succ (succ (succ zero))`. The principle of induction doesn't just *resemble* this construction, it directly exploits it! When you prove something by induction in Lean, you're working with the actual computational structure of how natural numbers exist in the system.

**SIMPLICIO:** That's amazing! So induction isn't just a proof technique—it's baked into the very fabric of how Lean understands numbers?

**SOCRATES:** Exactly. The principle of mathematical induction is a theorem in many mathematical frameworks, but in type theory, it's a fundamental consequence of how the natural numbers are defined.

**SIMPLICIO:** Okay, I'm convinced this is a legitimate proof technique. Can you give me an example?

**SOCRATES:** Certainly.
"
