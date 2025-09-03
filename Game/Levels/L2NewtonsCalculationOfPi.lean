import Game.Levels.L2NewtonsCalculationOfPi.L01_Newton

World "NewtonsCalculationOfPi"
Title "Lecture 2: Newton's Computation of π"

Introduction "
# The Mathematical Revolution of 1666

**SIMPLICIO:** I heard that Newton had a really cool way of calculating π. Can you tell me about it?

**SOCRATES:** Certainly. It begins around 1665-1666, when Newton was turning 23 years old. Anything significant about that year?

**SIMPLICIO:** Isn't that Newton's  \"annus mirabilis\",  year of miracles? If I recall correctly, he was forced to leave Cambridge due to an outbreak of  the Great Plague, and made his most groundbreaking discoveries (calculus, optics, gravitation, etc) while quarantining in isolation at his family home in Woolsthorpe.

**SOCRATES:** Exactly right. And one of the first things he discovered in that year was a  new version of
the Binomial Theorem. Tell me, please,  what can one say about
$(1 + x) ^ n$?

**SIMPLICIO:** Sure thing, if you multiply $(1+x)^n$ all out, you get
$ \\binom{n}{0} + \\binom{n}{1}x + \\binom{n}{2}x^2 + \\cdots + \\binom{n}{n}x^n$. Here $\\binom{n}{k}$ is the \"binomial coefficient\", the number of ways of choosing $k$ things from a bag of $n$ things. Explicitly, $\\binom{n}{k} = \\frac{n!}{k! (n-k)!}$. These are just the numbers in Pascal’s Triangle, and you can easily read off the $n$-th row.
[![Pascal's Triangle](images/Yanghui_triangle.jpg)](https://en.wikipedia.org/wiki/Pascal%27s_triangle)


**SOCRATES:** Excellent! And do you know sigma notation?

**SIMPLICIO:** I think so. I could’ve written  that same thing as $\\sum_{k=0}^{n} \\binom{n}{k} x^k$. In general, if you have some function $f: \\mathbb{N} \\to \\mathbb{R}$, and you want express $f(a)+f(a+1)+…+f(b)$, that is, the sum of $f(k)$ as $k$ ranges from some integer $a$ up to some other integer $b$, you can write it as $\\sum_{k=a}^{b} f(k)$.

**SOCRATES:** Very good.  So we have $(1+x)^n = \\sum_{k=0}^{n} \\binom{n}{k} x^k$. Now, would you allow me to write this as a sum going all the way out to infinity?
$(1+x)^n = \\sum_{k=0}^{\\infty} \\binom{n}{k} x^k$

**SIMPLICIO:** Hmm. Ok, I think I see what you’re getting at: Pascal’s Triangle has implied zeros everywhere outside, so $\\binom{n}{k}$ is just zero once $k>n$. So you’ve written it as an infinite sum, even though it secretly terminates after finitely many terms. But what purpose does extending it serve?

**SOCRATES:** Well, let me ask you this: can you think of any way of making sense of this formula when $n=-1$?

**SIMPLICIO:** Huh? You can’t use binomial coefficients. How do you choose 3 things from -1 things, that makes no sense!

**SOCRATES:** Ok, sure, but so many great discoveries in mathematics occur when you realize a way to **break the rules**, and follow some pattern **past** its intended limit (no calculus pun intended…). Put yourself in Newton’s shoes, if you can; what might a genius like him come up with?

**SIMPLICIO:** Well, we do have this other formula for binomial coefficients, not in terms of combinatorics, but just as factorials, $\\binom{n}{k} = \\frac{n!}{k! (n-k)!}$. That still doesn’t help because what the heck is $(-1)!$ supposed to be?! Oh, but wait! We can also write this as:

 $\\binom{n}{k} = \\frac{n(n-1)(n-2)\\cdots(n-k+1)}{k!}$

And in this way, we “bypass” the issue of dealing with $(-1)!$, and just go straight to “normal” numbers.

**SOCRATES:** Can you please write this using product notation?

**SIMPLICIO:** Sure, it's just like summation notation but with a $\\Pi$:

 $\\binom{n}{k} = \\frac{1}{k!}\\prod_{\\ell=1}^{k}(n-\\ell)$.

**SOCRATES:** Whoops, are you sure about those bounds in the product?

**SIMPLICIO:** Argh! It's so easy to make a silly mistake.
After writing down the formula, I should have
checked that I got the right start and end. Is this better?

$\\binom{n}{k} = \\frac{1}{k!}\\prod_{\\ell=0}^{k-1}(n-\\ell)$.

**SOCRATES:** Perfect. Go on.

**SIMPLICIO:** Ok, so if we agree to follow this pattern, then we get:

- $\\binom{-1}{0} = 1$, which makes sense because any row of Pascal's triangle starts with at $1=\\binom{c}{0}$; then

- $\\binom{-1}{1} = (-1)/1! = -1$, which also makes sense because the next term in the \"$c$th row\" of Pascal's triangle is always
$\\binom{c}{1} = c$; then we get:

- $\\binom{-1}{2} = (-1)(-2)/2! = +1$,

- $\\binom{-1}{3} = (-1)(-2)(-3)/3!=-1$.

Ok so I see the pattern:
it just alternates between $+1$ and $-1$, so the series goes:

 $(1+x)^{-1} = 1 - x + x^2 - x^3+x^4-x^5+\\cdots$.

**SOCRATES:** Very good! But does this formula make any actual
*sense*? How might you test it?

**SIMPLICIO:** Ok, if that series is supposed to \"represent\"
$1/(1+x)$, then if I multiply the whole thing by
$(1+x)$, I should just get $1$. Let's try it:

$(1+x)(1 - x + x^2 - x^3+x^4-x^5+\\cdots) = ?$

I'll first multiply everything by $1$, then by $x$, and add them all up.

$(1 - x + x^2 - x^3+x^4-x^5+\\cdots) + (x - x^2 + x^3- x^4+x^5\\cdots)$

Ok, so if I rearrange terms, then everything cancels out, and only the leading $1$ remains. Great!

**SOCRATES:** Interesting. And are you \"allowed\" to rearrange terms like that?

**SIMPLICIO:** Well.... why not?

**SOCRATES:** Ok, nevermind that for now,
you seem to be satisfied that it makes sense to say
that the series
$1 - x + x^2 - x^3+x^4-x^5+\\cdots$ \"converges\" (again, whatever that means) to $(1+x)^{-1}$.

**SIMPLICIO:** Come to think of it, I knew this already;
it's just the geometric series! I know that

$1+\\lambda + \\lambda^2+\\lambda^3+\\cdots$

adds up to $1/(1-\\lambda)$, and the series we have just replaces $\\lambda$ with $-x$.

**SOCRATES:** Yes, very good.
And where might this \"belong\" in Pascal’s triangle?

**SIMPLICIO:**
Holy cow! Did we just discover an extension of the triangle, going “up”?!
[![Pascal's Triangle, Extended](images/PascalM1.jpg)](https://en.wikipedia.org/wiki/Pascal%27s_triangle)

**SOCRATES:**
Indeed, and we can in fact continue this pattern for $n=-2,
-3, -4,$ and so on. I'll let you work it out yourself, but we actually
get a *whole other* Pascal's triangle (with some negative signs) *above* the standard one!
[![Pascal's Triangle, Extended](images/PascalMn.jpg)](https://en.wikipedia.org/wiki/Pascal%27s_triangle)
See how it still follows the usual rule, that the two numbers above and to the left or right add to the value just below them?

But let's try something even more exotic. Can you make
the Binomial Theorem work when $n=1/2$?


**SIMPLICIO:** Whoa, $n = 1/2$? That's... really pushing it! But let me try using the same formula. So $\\binom{1/2}{k} = \\frac{1}{k!}\\prod_{\\ell=0}^{k-1}(1/2-\\ell)$. Let me work out the first few terms:

- $\\binom{1/2}{0} = 1$ (as always)

- $\\binom{1/2}{1} = (1/2)/1! = 1/2$ (again, matches the pattern we already knew)

- $\\binom{1/2}{2} = (1/2)(-1/2)/2! = -1/8$

- $\\binom{1/2}{3} = (1/2)(-1/2)(-3/2)/3! = 1/16$

- $\\binom{1/2}{4} = \\frac{(1/2)(-1/2)(-3/2)(-5/2)}{4!} =  -\\frac{5}{128}$

So $(1+x)^{1/2} = 1 + \\frac{1}{2}x - \\frac{1}{8}x^2 + \\frac{1}{16}x^3 -
\\frac{5}{128}x^4+\\cdots$

But wait -- this is supposed to be $\\sqrt{1+x}$?!

**SOCRATES:** Again, go into Newton's thinking: how might he go about justifying whether this formula makes any sense?

**SIMPLICIO:** Oh, ok, I think I see! If we square the formula and multiply everything out, I guess we're supposed to get $1+x$ -- that would justify calling the series $\\sqrt{1+x}$.

**SOCRATES:** Go for it!

**SIMPLICIO:** Ok, so I want

$\\left(1 + \\frac{1}{2}x - \\frac{1}{8}x^2 + \\frac{1}{16}x^3 -
\\frac{5}{128}x^4+\\cdots\\right)^2$

That means squaring every term, and also adding twice every product of distinct pairs of terms.

**SOCRATES:** Right. Can you think of a good way of keeping track of everything?

**SIMPLICIO:** Oh, I know! Let's group things by the power of $x$ involved. The first one is easy: $x^0=1$, which you only get from squaring the first term. So that coefficient is $1$.

For the coefficient of $x^1$, I can't square anything involving $x$'s, so I
can only multiply the $x$ term by the constant term, and of course double it.
That's just $2 \\times 1 \\times \\frac{1}{2}x = x$. So the coefficient of $x$ is $1$.

For $x^2$, I get two contributions  from constant times quadratic: $2 \\times 1 \\times \\left(-\\frac{1}{8}x^2\\right) = -\\frac{1}{4}x^2$ and also from the square of the linear term: $\\left(\\frac{1}{2}x\\right)^2 = \\frac{1}{4}x^2$. So the total coefficient is $-\\frac{1}{4} + \\frac{1}{4} = 0$.

Let's try a few more. To get $x^3$, I need:
- $2 \\times 1 \\times \\frac{1}{16}x^3 = \\frac{1}{8}x^3$ (constant times the $x^3$ term)
- $2 \\times \\frac{1}{2}x \\times \\left(-\\frac{1}{8}x^2\\right) = -\\frac{1}{8}x^3$ (the $x$ term times the $x^2$ term)

So the total coefficient of $x^3$ is $\\frac{1}{8} - \\frac{1}{8} = 0$.

This is amazing! It really seems like all the higher-order terms are canceling out perfectly. I bet that will keep happening, and we'll just get the square to come out to exactly $1+x$; the formula really works!

So wait, now we get a whole other row in Pascal's triangle, *between* rows $0$ and $1$?!

[![Pascal's Triangle](images/PascalM12.jpg)](https://en.wikipedia.org/wiki/Pascal%27s_triangle)

**SOCRATES:** Beautiful, isn't it!

**SIMPLICIO:** Wait, this is all much simpler than I'm making it. Isn't this just the same thing as the Taylor expansion about $x=0$ of the function $f(x)=\\sqrt{1+x}$?
I already know how to do this from Calculus.

**SOCRATES:** Yes, very good; but Brook Taylor (of Taylor series) did not prove his general theorem until 1715, a few decades after
Newton's computation of $\\pi$.

Now, suppose you wanted to compute something like $\\sqrt 3$ -- can you think of a way of doing it using this formula?

**SIMPLICIO:** Ok, sure, $3$ is near $4$, which I know is a perfect square,
and presumably I should be trying to use the identity for $\\sqrt {1+x}$. Ah! We can write

$\\sqrt 3 = \\sqrt{4-1} = \\sqrt{4(1-\\frac14)}=2\\sqrt{1-\\frac14}$

So now if I apply our formula with $x=-1/4$, I guess I'll get:

$\\sqrt3 \\approx 2\\left(
1 + \\frac{1}{2}(-1/4) - \\frac{1}{8}(-1/4)^2 + \\frac{1}{16}(-1/4)^3 -
\\frac{5}{128}(-1/4)^4+\\cdots
\\right)$

Taking just these five terms, the fraction on the right comes out to $28379/16384\\approx 1.73212$, which is impressively close to $\\sqrt3\\approx1.7320508$.
We got 3 decimal places of accuracy, nice!

**SOCRATES:** Great! Now you see the power of Newton's Binomial Theorem. Ok, so then let's return all the way back to your original question, about Newton's estimate for $\\pi$.

**SIMPLICIO:** Hmmm, $\\pi$ is the ratio of circumference to diameter in a circle. So where am I supposed to find a length.

**SOCRATES:** Ah, but what did we learn from Archimedes?

**SIMPLICIO:** Oh, that $\\pi$ is also an *area*, not just a length. It's the area of a unit circle $\\pi r^2$ where $r=1$.

**SOCRATES:** Beautiful. And could you find a circle's area lurking somewhere?

**SIMPLICIO:**  I think I see it! Thanks to Descartes, and \"Cartesian\" coordinates, we can express the  circle as the graph of $x^2+y^2=1$, or to make it a function, $y=\\sqrt{1-x^2}$. So we just have to replace $x$ in our series with $-x^2$.

$
\\sqrt{1-x^2}
= 1 + \\frac{1}{2}(-x^2) - \\frac{1}{8}(-x^2)^2 + \\frac{1}{16}(-x^2)^3 - \\frac{5}{128}(-x^2)^4+\\cdots
$

$
= 1 - \\frac{x^2}{2} - \\frac{x^4}{8} - \\frac{x^6}{16} - \\frac{5x^8}{128} - \\cdots
$

And the area under the curve $y=\\sqrt{1-x^2}$ from $x=0$ to $x=1$ is
a quarter circle.
[![Quarter Circle](images/PiOver4.jpg)](https://en.wikipedia.org/wiki/Area_of_a_circle)


**SOCRATES:** Luckily, Newton had just invented calculus! So how else
could he compute the area under this curve?

**SIMPLICIO:** With an integral! So:

$\\frac{\\pi}4 = \\int_0^1 \\sqrt{1-x^2} \\, dx =
\\int_0^1 \\left(1 - \\frac{x^2}{2} - \\frac{x^4}{8} - \\frac{x^6}{16} - \\frac{5x^8}{128} - \\cdots\\right) dx$

I'll just integrate term by term,...

**SOCRATES:** Whoa, hang on! Why are you allowed... You know what, nevermind, sorry.
Just go ahead.

**SIMPLICIO:** Ok, weirdo. Anyway. So integrating term by term, I get:

$\\frac{\\pi}4 = \\left[x - \\frac{x^3}{6} - \\frac{x^5}{40} - \\frac{x^7}{112} - \\frac{5x^9}{1152} - \\cdots\\right]_0^1$

$= 1 - \\frac{1}{6} - \\frac{1}{40} - \\frac{1}{112} - \\frac{5}{1152} - \\cdots $

Wow! So Newton got an infinite series for $\\pi$!
If I evaluate just these five terms, and cross multiply by the factor of $4$, I get the fraction
$32057/10080\\approx 3.180$, not bad!

**SOCRATES:** Not bad indeed. You know, Simplicio, many math papers have roughly zero new ideas; they're just
doing something nobody bothered to do before in a slightly
newer context. A really good math paper can have one or two genuinely new ideas. Newton is already on new idea number five, and he's still not done!

**SIMPLICIO:** Ok, so what's new idea number six?

**SOCRATES:** Well, remember how you integrated all the way up to $x=1$? In your series,

$\\frac{\\pi}4 = \\left[x - \\frac{x^3}{6} - \\frac{x^5}{40} - \\frac{x^7}{112} - \\frac{5x^9}{1152} - \\cdots\\right]_0^1$

you have all these high powers of $x$ but they're being \"wasted\" because you're setting $x$ to $1$. What if instead  you only integrated up to, say, $x=1/2$?

**SIMPLICIO:** Ooh, cool! Then the series will converge much more rapidly. But wait, that changes the geometry. Instead of a quarter-circle, we now have... a 30 degree sector, which has area $\\pi/12$, plus a 30-60-90 triangle -- ah that must be why you suggested $x=1/2$ -- with area $\\frac12\\times\\frac12\\times\\frac{\\sqrt3}2$.

[![Integrating to x=1/2](images/PiOver12.jpg)](https://en.wikipedia.org/wiki/Area_of_a_circle)

Good thing we already know how to quickly estimate $\\sqrt3$ to high accuracy! (Ah, that's the trade-off: we could set $x$ even smaller, for faster convergence, but then we'll need to deal with ever more complicated geometric evaluations; so $x=1/2$ is a \"sweet spot\".) So now:

 $ \\frac{\\pi}{12} +  \\frac{\\sqrt3}8 =
\\left[x - \\frac{x^3}{6} - \\frac{x^5}{40} - \\frac{x^7}{112} - \\frac{5x^9}{1152} - \\cdots\\right]_0^{1/2}$

$ = \\frac12 - \\frac{1}{6}\\left(\\frac12\\right)^3 - \\frac{1}{40}\\left(\\frac12\\right)^5 - \\frac{1}{112}\\left(\\frac12\\right)^7 - \\frac{5}{1152}\\left(\\frac12\\right)^9 - \\cdots.$

Again evaluating just these five terms already gives the fraction $9874097/20643840$.
And now isolating $\\pi$ gives the estimate

$\\pi \\approx 12\\times\\left(9874097/20643840 -  \\frac{\\sqrt3}8\\right) \\approx 3.14161,$

which is off by two parts in $100,000$ from the true estimate $\\pi \\approx 3.14159$. All that with just five terms, amazing!


**SOCRATES:** Yes, Newton was very impressive indeed.
Here's a nice YouTube video by Veritasium that discusses this whole saga (right-click to get it to pop up in a new tab):
[![Veritasium Video](https://img.youtube.com/vi/gMlf1ELvRzc/maxresdefault.jpg)](https://youtu.be/gMlf1ELvRzc)

 In fact, a series similar to this one was discovered two centuries earlier, by the Indian mathematician Madhava of Sangamagrama. And it would take two more centuries until mathematicians figured out how to rigorously justify all of these reorderings, limit swaps, etc, etc.

**SIMPLICIO:** Ok, ok; you've convinced me! On with some actual Real Analysis please.

"
