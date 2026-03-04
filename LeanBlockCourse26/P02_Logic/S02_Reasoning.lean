/-
This part is mostly inspired by `Robo` and `A Lean Intro to Logic`:
https://adam.math.hhu.de/#/g/hhu-adam/robo
https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic
-/

import Mathlib.Tactic.Basic

/-
# Reasoning Tactics
=====================

After learning the basic building blocks, we now look at two complementary styles of reasoning:

Forward reasoning:
- `have`: introduce new facts from existing ones

Backward reasoning:
- `apply`: transform goals using implications
- `suffices`: introduce a fact and use it to rewrite the goal
- `refine`: a version of `exact` that permits placeholders
-/

/-
## A small side note on Lemmas and Facts

A *Lemma* is (usually) a statement that is re-usable and cleanly
abstracted with defined assumptions, that is stated **outside** of
the proof of a bigger *Theorem* but used inside it.

Lean also has `lemma` but since the distinction between
Lemmas and Theorems (and Propositions...) is blurry, mathlib just
embraces calling everything a `theorem`.

A *Fact* is (usually) a cleanly separate sub-statement in the
proof of a bigger *Theorem* that is not worth abstracting into
its own *Lemma* since there is no expectation it will be used
in any other proofs besides this one specific one.

This is remarkably similar to the `DRY` (Do Not Repeat Yourself)
principle in coding: if a block of code is only used in this one
particular method, this is where it should live. If it will or
can reasonably be used in other methods, you should abstract it
into its own method.

Lean also allows you to structure your proof by stating separate
facts in it through the `have` tactic.
-/

/-
## Forward Reasoning with `have`

The `have` tactic introduces new facts derived from existing ones.
It's useful for breaking down complex proofs into steps and is
used around 34,000 times in mathlib.
-/

-- Using have to build up facts step by step
theorem example_forward (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R := by
  have q : Q := by exact h₁ p -- Since P implies Q and we have a proof of P, we have a proof of Q
  have r : R := by exact h₂ q -- Since Q implies R and we have a proof of Q, we have a proof of R
  exact r                     -- We need and have a proof of R

#print example_forward -- The `have` actually shows up in term mode

-- We can of course simplify this proof in term mode
example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R := by
  have q : Q := h₁ p
  have r : R := h₂ q
  exact r

example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R := by
  exact h₂ (h₁ p)

example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R :=
  h₂ (h₁ p) -- or `h₂ <| h₁ p` or `(h₂ ∘ h₁) p`

/-
There is some overlap between `let` and `have`. The simple mental
model you should use is:

* A definition ("Let S be the set of primes.") should be `let`.
* A fact ("Since we know X and Y, we know Z.") should be `have`.
-/

/-
## Backward Reasoning with `apply`

The `apply` tactic works backward from the goal, reducing it to simpler subgoals.
If we want to prove `Q` and we have `h : P → Q`, then `apply h` changes the goal
from `Q` to `P`. This tactic is used around 15,000 times in mathlib.
-/

-- The same proof using apply to work backward
theorem example_backward (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R := by
  apply h₂ -- To prove R, it suffices to prove Q
  apply h₁ -- To prove Q, it suffices to prove P
  exact p  -- We need and have a proof of P

#print example_backward -- This just produces the forward term proof `h₂ (h₁ p)`


/-
Note that `apply`ing an implication to your goal is inherently destructive:
it is very possible that you end up with a goal that is actually hard
or even impossible to prove: everything follows from `⊥`, so you can
always rewrite your goal to `⊥`. But that will not be helpful.

Lean also inherently argues forward through type theory, so the backward
reasoning is a tactic mode convenience layer for mathematicians.

Also note that `rw [...] at ...` and `rw [...]` from P02S01 also can be
viewed in this forward and backward arguing model, but they are non-destructive.
-/

/-
## Exercise Block B01: Graph of Implications

This exercise demonstrates how forward and backward reasoning can lead to very
different-looking proofs of the same fact. Consider the following graph of
implications:

A - f -> B <- g - C
|        |        |
h        i        j
|        |        |
v        v        v
D <- k - E - l -> F
^        ^        |
|        |        p
m        n        |
|        |        v
G <- q - H - r -> I

Find a path from `A` to `I` using different reasoning styles. Have at least
one purely forward arguing path and one purely backward arguing path.
-/

-- Exercise 1.1
-- Find a purely forward arguing path from `A` to `I`.
example (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F)
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I)
    (q : H → G) (r : H → I) (a : A) : I := by
  have b : B := f a
  have e : E := i b
  have f : F := l e
  have i : I := p f
  exact i

example (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F)
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I)
    (q : H → G) (r : H → I) (a : A) : I := by
  have b := f a -- output type is inferred / determined by the term mode proof
  have e := i b -- output type is inferred / determined by the term mode proof
  have f := l e -- output type is inferred / determined by the term mode proof
  have i := p f -- output type is inferred / determined by the term mode proof
  exact i

example (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F)
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I)
    (q : H → G) (r : H → I) (a : A) : I :=
  p <| l <| i <| f a  -- Can just collapse everything into term mode

-- Exercise 1.2
-- Find a purely backward arguing path from `A` to `I`.
example (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F)
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I)
    (q : H → G) (r : H → I) (a : A) : I := by
  apply p
  apply l
  apply i
  apply f
  exact a

-- Exercise 1.3
-- Find a path that mixes forward and backward reasoning.
example (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F)
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I)
    (q : H → G) (r : H → I) (a : A) : I := by
  apply p
  apply l
  exact i (f a)

/-
## Forgetting about assumptions with `clear`

The `clear` tactic lets you forget assumptions. You should generally not need
this and instead structure your code to only have necessary assumptions in scope.
-/

example (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F)
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I)
    (q : H → G) (r : H → I) (a : A) : I := by
  clear g h j k m n q r      -- The linter still complains though
  exact p <| l <| i <| f a

/-
## The `suffices` Tactic

Enables explicit backward reasoning by declaring intermediate goals:

1. Declares a subgoal that would suffice to prove the original goal
2. Once proven, provides access to the subgoal proof via `this`
3. Maintains goal context for clearer proof structuring

This tactic is used around 2,800 times in mathlib. But it is very nice
in that it mimics the human language "it suffices to show that ... because ...".
-/

-- Basic suffices example showing goal transformation
example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R := by
  suffices Q by  -- unlike `apply h₂` the result is already visible in code
    -- At this point we have entered a sub-proof where we show that it does
    -- in fact suffice to show Q, similar to how `have` has its own sub-proof.
    -- In this sub-proof the actual assumption you are claiming suffices is
    -- introduced as `this`. Note that the term `this` (if not used as an
    -- actual variable name as it is here) also refers to the last unnamed variable.
    exact h₂ this
  exact h₁ p

/-
Unlike `have`, the tactic `suffices` does not support `:=` for its
sub-proof, i.e., it always needs `by` to open a tactic block.
-/

-- Compare with equivalent `apply`
example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R := by
  apply h₂
  exact h₁ p

-- You can actually name the hypothesis in `suffices`
example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R := by
  suffices q : Q by
    exact h₂ q
  exact h₁ p

/-
## The `refine` Tactic

The `refine` tactic behaves like `exact` but permits placeholders (i.e. `?_`)
in the provided term. Any unsolved hole that is not fixed by unification with
the main goal's target is converted into a new goal. This tactic is used
around 22,000 times in mathlib.
-/

example (P Q : Prop) (f : P → Q) (p : P) : Q := by
  refine f ?_  -- in this case it behaves like `apply`
  exact p      -- this answers a sub-goal raised by `?_`

example (P Q : Prop) (f : P → Q) (p : P) : Q := by
  refine f p   -- in this case it behaves like `exact`

-- You can also stack proofs inside proofs for `refine`
example (P Q : Prop) (f : P → Q) (p : P) : Q := by
  refine f (by exact p)

-- In fact this also works for `exact`
example (P Q : Prop) (f : P → Q) (p : P) : Q := by
  exact f (by exact p)

/-
## Tactics are just "syntactic sugar" to make mathematicians' lives easier

At its core everything is term mode forward arguing composition of functions,
but tactics allow you to argue closer to natural language. This inherently
will mean there are many equivalent ways of achieving the same goal
and there will always be some weirdness and inconsistencies because of that
flexibility.

## Notational inconsistencies

Unfortunately the syntax of mathlib tactics is not entirely
consistent, so in particular `:=` is not always used to signal
the start of a sub-proof (`let` and `have` use it, `refine` and
`suffices` do not) and just because one tactic admits a certain
syntax, another does not necessarily allow the same, so the
following are all *invalid* for `suffices`:

* suffices Q                   -- just leave argument open
* suffices Q by ?_             -- leave an intentional gap
* suffices Q := h₂ this        -- use term mode

## Whitespace (indentation and newlines)

Indentation does not matter (since lean / mathlib 4), but you
can use it freely to structure your proofs and indicate when
you are in a sub-proof. Newlines matter, but as in many languages,
you can replace them with `;`, e.g.:
-/

example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (p : P) : R :=
  by apply h₂; exact h₁ p


/-
## Exercise Block B02: Graph of Implications (Continued)
-/

-- Exercise 2.1
-- Use only `suffices` to work backwards from the goal:
example (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F)
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I)
    (q : H → G) (r : H → I) (a : A) : I := by
  suffices F by exact p this
  suffices e : E by exact l e
  suffices B by exact i this
  exact f a

-- Exercise 2.2
-- Use only `refine` to work backwards from the goal:
example (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F)
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I)
    (q : H → G) (r : H → I) (a : A) : I := by
  refine p ?_
  refine l ?_
  refine i ?_
  refine f ?_
  exact a

-- Exercise 2.3
-- Combine all of `clear`, `exact`, `have`, `suffices`, `refine`, and `apply`
-- *NEVER* actually write your proofs like this!!!
example (A B C D E F G H I : Prop)
    (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F)
    (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I)
    (q : H → G) (r : H → I) (a : A) : I := by
  clear h
  apply p
  clear r
  clear n
  clear q
  suffices E by exact l this
  clear m
  clear j
  have b : B := f a
  clear g
  clear k
  refine i (by exact b)
