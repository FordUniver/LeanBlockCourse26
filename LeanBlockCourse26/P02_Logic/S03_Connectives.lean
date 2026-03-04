/-
This part is mostly inspired by `Robo` and `A Lean Intro to Logic`:
https://adam.math.hhu.de/#/g/hhu-adam/robo
https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic
-/

import Batteries.Tactic.Trans
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.TFAE
import Mathlib.Logic.Basic

/-
# Logical Connectives
=====================

This module introduces how to work with compound propositions:
- Conjunction (`AND`, `∧`)
- Disjunction (`OR`, `∨`)
- Equivalence (`↔`) is (essentially but not exactly) just a `(_ → _) ∧ (_ → _)`

Key tactics:
- `constructor` for splitting compound goals
- `cases` and `rcases` for basic pattern matching
- `obtain` for destructuring hypotheses
- `trans` for chaining equivalences
- `tfae` for working with lists of equivalences
-/

/-
## Working with AND (∧) in the goal

To prove `P ∧ Q`, we need to prove both `P` and `Q`. We can:
- Use `apply And.intro` explicitly
- Use `constructor` as shorthand
- Use angle bracket notation `⟨p, q⟩`

`constructor` is used around 3,000 times in mathlib while
`exact` followed by an `⟨⬝⟩` term is used around 7,000 times.
-/

#check And
#check And.intro  -- arguments are `(a : Prop)` and `(b : Prop)` and output is `(a ∧ b : Prop)`

-- Using `apply And.intro` will open two goals (one for `a` and one for `b`)

-- The linter will complain about the following formatting, even though this
-- produces valid Lean code. So the `exact` tactic is slightly cleverer than
-- we originally assumed: it can handle multiple goals and close the first one
-- while keeping others open, so no longer quite the same behavior like a `return`.
-- Note that the order matters though, so `exact q; exact p` does not work.
theorem goal_and_apply (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  apply And.intro
  exact p
  exact q

#print goal_and_apply -- produces `⟨p, q⟩`, we will see this notation in a second

-- The notation hides the actual term mode proof
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := And.intro p q

-- This is the recommended and much more readable syntax!
-- But note that we still need to respect the order.
theorem goal_and_apply' (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  apply And.intro
  · exact p -- The `\.` produces · and focuses on the next goal
  · exact q

#print goal_and_apply' -- also produces `⟨p, q⟩`

-- In order not to have to remember `And.intro` (and the equivalent names
-- for any other structures in the future), we can use the `constructor` tactic
theorem goal_and_constructor (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  constructor
  · exact p
  · exact q

#print goal_and_constructor -- also produces `⟨p, q⟩`

-- Looking at the actual term modes already introduces the angle bracket
-- notation, which we can also use: `⟨p, q⟩` is notation for `And.intro p q`
-- (assuming `p : P : Prop` and `q : Q : Prop`).
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  exact ⟨p, q⟩

-- Or just use term mode with the `⟨...⟩` notation
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := ⟨p, q⟩

-- First side note: the `⟨...⟩` notation just instantiates a structure ...
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  exact {
    left := p,
    right := q
  }

-- ... but it hides the names by simply ordering the components. By naming
-- them we can also determine the order in which we prove them. Recall P01S05.
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  exact {
    right := q,
    left := p
  }

-- Second side note: recall that we can stack proofs in proofs
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  exact ⟨by assumption, by assumption⟩

-- We can start a tactic mode sub-proof even in term mode
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := ⟨p, by assumption⟩

/-
## Working with AND in a hypothesis

To use a hypothesis `h : P ∧ Q`, we can:

- Access components with `h.1` / `h.2` or `h.left` / `h.right`
- Use `obtain` for destructuring
- Use `cases` and `rcases` for basic pattern matching

`obtain` is used around 15,000 times in mathlib, `cases` 3,000 times,
and `rcases` 7,000 times.
-/

-- Using `.1` / `.2` notation
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  constructor -- because the goal has an `∧`
  · exact h.2
  · exact h.1

-- In term mode
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := ⟨h.2, h.1⟩

-- Recalling that `And` is just a structure with `left`
-- and `right`, we can also use `.right` / `.left` notation
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  constructor
  · exact h.right
  · exact h.left

-- In term mode ...
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := ⟨h.right, h.left⟩

-- ... or also
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := {
  right := h.left,
  left := h.right
}

/-
All of this works for arbitrary structures in Lean, so you can always
(de)construct an instance sequentially (by order of the arguments)

-> `⟨...⟩`, `And.intro ...`, `constructor` with `·`, `.1`, and `.2`

or by specifying the actual names of the components of the structure.

-> `{left := ..., right := ...}`, `.left`, and `.right`

```
structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b
```
-/

-- Using `obtain` for destructuring
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨p, q⟩ := h -- dissects into `p` and `q` and forgets about `h`
  exact ⟨q, p⟩

-- Using `have` for destructuring
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  have ⟨p, q⟩ := h -- dissects into `p` and `q` but does *not* forget about `h`
  exact ⟨q, p⟩

-- Splitting h up using `cases` (though this is very unintuitive...)
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  cases h
  constructor
  · assumption
  · assumption

-- Using pattern matching with `cases` (recall P01S05)
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  cases h with
  | intro p q => exact ⟨q, p⟩ -- though mathematically this is awful notation

-- Though `rcases` (recursive `cases`) provides a more pleasant syntax here
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  rcases h with ⟨p, q⟩
  exact ⟨q, p⟩

-- `cases'` provides yet another syntax for destructuring, though the linter complains
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  cases' h with p q
  exact ⟨q, p⟩

-- Note that introduction can be combined with pattern matching
example (P Q : Prop) : (P ∧ Q) → P := by
  intro h
  obtain ⟨p, _⟩ := h
  exact p

example (P Q : Prop) : (P ∧ Q) → P := by
  intro ⟨p, _⟩
  exact p

-- This also works nicely in term mode
example (P Q : Prop) : (P ∧ Q) → P := fun ⟨p, _⟩ => p

-- Note that this is different from
example (P Q : Prop) : P → Q → P := fun p _ => p

/-
## Exercise Block B01
-/

-- Exercise 1.1
-- State and prove that if `P → Q` and `P → R`, then `P → (Q ∧ R)`.


-- Exercise 1.2
-- Also give a clean term mode version of this
