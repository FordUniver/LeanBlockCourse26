/-
This part is mostly inspired by `Robo` and `A Lean Intro to Logic`:
https://adam.math.hhu.de/#/g/hhu-adam/robo
https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic
-/

import Mathlib.Tactic.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Push
import Mathlib.Tactic.NthRewrite
import ProofGolf

/-
# Negation and Classical Logic
=====================

This module builds on previous logical foundations to explore:

- Working with negation (`¬`) and contradiction
- Classical reasoning with `by_contra`
- Simplifying negations using `push_neg`
- Handling contradictions with `exfalso` and `contradiction`
-/

/-
## Understanding Negation

In Lean, `¬P` is defined as `P → False`. This perspective allows us to:

- Treat negations as implication arrows to `False`
- Use implication-handling tactics with negations
-/

#check Not -- `Not (a : Prop) : Prop`, i.e., `Prop → Prop`

/-
In Lean, `Not` is just constructed as `a → False`, so the only ingredients
needed are the type `Prop : Type` and `False : Prop` and the functional
composition through `→`.

def Not (a : Prop) : Prop := a → False
-/


-- This definition makes `rfl` work here ...
example (P : Prop) : ¬P ↔ (P → False) := by
  rfl

-- ... but we can also be a bit more verbose.
example (P : Prop) : ¬P ↔ (P → False) := by
  constructor
  · intro h  -- `h` states that `P` is not true, that is `P → False`
    intro p  -- `p` states that `P` is true
    exact h p
  · intro h
    exact h

example (P : Prop) : ¬P ↔ (P → False) := by
  constructor
  all_goals intro h; exact h

example (P : Prop) : ¬P ↔ (P → False) := 
  ⟨id, id⟩

-- If you have a negation in the assumption you can sometimes derive `False`
example (P Q : Prop) (h : P → ¬Q) (p : P) (q : Q) : False := by
  obtain h := h p
  exact h q

example (P Q : Prop) (h : P → ¬Q) (p : P) (q : Q) : False :=
  (h p) q

/-
## The `contradiction` Tactic

The `contradiction` tactic automatically closes goals with:

- Direct `False` hypotheses
- Obviously conflicting assumptions
- Mismatched constructors in inductive types

It is used around 400 times in mathlib.
-/

example (P : Prop) (h : False) : P := by
  contradiction

example (P Q : Prop) (h : P) (hn : ¬P) : Q := by
  contradiction

/-
Side remark: assuming `False` or anything that produces `False`, i.e.,
a contradiction in our assumptions, allows us to prove *anything*
(Fermat's last theorem, any open conjecture, obvious falsehoods, ...).

By Gödel we unfortunately know that no magical tactic (meaning an
algorithm) can exist that can verify your assumptions are free of
contradictions, since we provably cannot show that any sufficiently
sophisticated logical system is free of contradiction.
-/

/-
## The `trivial` tactic

`trivial` tries different simple tactics, in particular `contradiction`,
to close the current goal. It is used around 500 times in mathlib.
-/

example (P : Prop) (h : P) : P := by
  trivial

/-
## The `exfalso` tactic

The `exfalso` tactic converts any goal to `False`, allowing you to:

- Work explicitly with contradictions
- Use any false assumption to prove arbitrary claims
- Combine with other tactics for manual contradiction handling

It is used around 200 times in mathlib.
-/

-- This is `False.elim` in Lean (Init.Prelude)
theorem exfalso_example (P : Prop) (h : False) : P := by
  exfalso    -- Changes goal to False
  exact h    -- Uses the False hypothesis

#print exfalso_example  -- Under the hood this uses `False.elim h`

#print axioms exfalso_example -- We are still not using classical logic!

/-
## The `push_neg` Tactic (Classical logic)

Normalizes negated expressions by pushing negation inward:

- Converts `¬(P ∧ Q)` to `P → ¬Q`
- Converts `¬(P → Q)` to `P ∧ ¬Q`
- Converts `¬¬P` to `P` (uses law of excluded middle: `P ∨ ¬P`)
- Simplifies nested negations
-/

-- This is `Classical.not_not.mp` in Lean (Init.Classical), exported as `not_not.mp` by Mathlib.Logic.Basic
theorem push_neg_example (P : Prop) : ¬¬P → P := by
  push_neg
  exact id

#print axioms push_neg_example  -- This does use the axiom of excluded middle (classical logic)

/-
## Exercise Block B01

Related: https://www.youtube.com/watch?v=aMxcAaR0oHU
-/

-- Exercise 1.1a
-- This is `not_not_intro` in Lean (Init.Core), also `Classical.not_not.mpr` / `not_not.mpr`
-- Prove the statement using `push_neg`
theorem nnp_of_p_exercise_push_neg (P : Prop) : P → ¬¬P := by
  intro p
  push_neg
  exact p

#print axioms nnp_of_p_exercise_push_neg

-- Exercise 1.1b
-- Prove the statement without `push_neg` amd without classical
-- logic, i.e., use `#print axioms` to make sure you are not
-- dependent on any (`Classical.`) axioms!
theorem nnp_of_p_exercise_fun (P : Prop) : P → ¬¬P := by
  intro p
  intro np
  exact np p

#print axioms nnp_of_p_exercise_fun

theorem nnp_of_p_exercise_fun_term (P : Prop) : P → ¬¬P := fun p np => np p

#print axioms nnp_of_p_exercise_fun_term

theorem nnp_of_p_exercise_contradiction (P : Prop) : P → ¬¬P := by
  intro p
  intro np
  contradiction

#print axioms nnp_of_p_exercise_contradiction

-- Exercise 1.2
example (P Q : Prop) (p : ¬¬P) (f : P → Q) : ¬¬Q := by
  push_neg
  push_neg at p
  exact f p

example (P Q : Prop) (p : ¬¬P) (f : P → Q) : ¬¬Q := by
  push_neg at *
  exact f p

-- Exercise 1.3
example (P Q R : Prop) (h : P ∨ Q ∨ R → ¬(P ∧ Q ∧ R)) : (P ∨ Q) ∨ R → ¬((P ∧ Q) ∧ R) := by
  intro hpqr ⟨⟨p, q⟩, r⟩
  apply h
  · rcases hpqr with (p | q) | r
    · left; exact p
    · right; left; exact q
    · right; right; exact r
  · exact ⟨p, q, r⟩

example (P Q R : Prop) (h : P ∨ Q ∨ R → ¬(P ∧ Q ∧ R)) : (P ∨ Q) ∨ R → ¬((P ∧ Q) ∧ R) := by
  rintro ((p | q) | r)
  all_goals
    rintro ⟨⟨p, q⟩, r⟩
  · exact (h (Or.inl p)) ⟨p, q, r⟩
  · exact (h (Or.inl p)) ⟨p, q, r⟩
  · exact (h (Or.inl p)) ⟨p, q, r⟩

#golf example (P Q R : Prop) (h : P ∨ Q ∨ R → ¬(P ∧ Q ∧ R)) : (P ∨ Q) ∨ R → ¬((P ∧ Q) ∧ R) := by
  rintro ((p | q) | r)
  all_goals
  rintro ⟨⟨p, q⟩, r⟩
  exact (h (Or.inl p)) ⟨p, q, r⟩

#golf example (P Q R : Prop) (h : P ∨ Q ∨ R → ¬(P ∧ Q ∧ R)) : (P ∨ Q) ∨ R → ¬((P ∧ Q) ∧ R) := by
  rintro ((p | q) | r) <;> rintro ⟨⟨p, q⟩, r⟩ <;> exact (h (Or.inl p)) ⟨p, q, r⟩

#golf example (P Q R : Prop) (h : P ∨ Q ∨ R → ¬(P ∧ Q ∧ R)) : (P ∨ Q) ∨ R → ¬((P ∧ Q) ∧ R) := by
  push_neg at *
  rintro _ ⟨p, q⟩
  exact h (Or.inl p) p q

-- Exercise 1.4
#golf example (P Q : Prop) (h : P → ¬ Q) (p : P) (q : Q) : False := by
  suffices ¬Q by contradiction
  exact h p

#golf example (P Q : Prop) (h : P → ¬ Q) (p : P) (q : Q) : False := by
  exact h p q

/-
## Classical Reasoning with `by_contra`

Enables proof by contradiction in classical logic:

1. Assume the negation of the goal
2. Derive a contradiction
3. Conclude the original goal
-/

-- We have already seen this with a `push_neg`...
theorem by_contra_example_push_neg (P : Prop) : ¬¬P → P := by
  push_neg
  exact id

-- ... but we can also resolve this with `by_contra`...
theorem by_contra_example (P : Prop) : ¬¬P → P := by
  intro nnp
  by_contra np
  contradiction

theorem by_contra_example' (P : Prop) : ¬¬P → P := by
  intro nnp
  by_contra np
  exact nnp np

-- ... and looking at the axioms we see both use `Classical.choice`!

#print axioms by_contra_example_push_neg -- propext, Classical.choice, Quot.sound
#print axioms by_contra_example -- propext, Classical.choice, Quot.sound

/-
## Classical Reasoning with `by_cases`

The `by_cases` tactic allows classical case analysis on any proposition:

- Splits the proof into two cases: one where the proposition is true, and one where it's false
- Particularly useful with excluded middle (`P ∨ ¬P`) in classical logic
- Often combined with `push_neg` for handling negations

This tactic is used around 1,200 times in mathlib.
-/

-- This is the "law of the excluded middle" ...
example (P : Prop) : P ∨ ¬P := Classical.em P

#print Classical.em -- This has an actual proof ...

#print axioms Classical.em -- ... but it uses `Classical.choice` ...

#check Classical.choice -- ... which is closer to the axiom of choice (AoC)


/-
Looking into Lean, this is actually the first time we see something
resembling a mathematical axiom:

```
axiom Classical.choice {α : Sort u} : Nonempty α → α
```
-/

-- You can directly invoke the axiom `Classical.choice` ...
example (P : Prop) : P ∨ ¬P := by
  have p_or_np := Classical.em P
  exact p_or_np

-- ... and if you had a more complicated proof you could do a case
-- distinction with `rcases` ...
example (P : Prop) : P ∨ ¬P := by
  have p_or_np := Classical.em P
  rcases p_or_np with (p | np)
  · left; exact p
  · right; exact np

-- ... but it is much easier to invoke `by_cases` ...
example (P : Prop) : P ∨ ¬P := by
  by_cases P  -- do a case distinction on whether or not P is true
  · left; assumption
  · right; assumption

-- ... and you can name the assumption like this ...
example (P : Prop) : P ∨ ¬P := by
  by_cases h : P  -- do a case distinction on whether or not P is true
  · left; exact h
  · right; exact h

/-
## Exercise Block B02: Classical vs. Intuitionistic Logic

Classical logic accepts the Law of Excluded Middle (`P ∨ ¬P`) and double
negation elimination (`¬¬P → P`), making proof by contradiction a powerful tool.
In contrast, intuitionistic logic allows only constructive proofs—for example,
the contrapositive (`P → Q` implies `¬Q → ¬P`) is acceptable, but the reverse
implication generally requires non-constructive reasoning. Lean bridges these
approaches by providing classical tactics (e.g., `by_contra`, `by_cases`) for
accessing classical axioms when needed.
-/

-- Exercise 2.1
-- This is `mt` (modus tollens) in Lean (Init.Core); `Function.mt` in Mathlib.Logic.Basic enables `h.mt`
-- Prove this constructively, i.e., using intuitionistic logic
-- and verify no axioms were used with `#print axioms _`
theorem exercise_2_1_constructive (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  intro h₁ h₂ h₃
  let hor := h₁ h₃
  contradiction

example (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  intro h₁ h₂ p
  exact h₂ (h₁ p)

example (P Q : Prop) : (P → Q) → (¬Q → ¬P) :=
  fun h₁ h₂ p => h₂ (h₁ p)

#print axioms exercise_2_1_constructive -- no axioms used

-- Exercise 2.2
-- Prove this using classical logic and verify that you
-- used `Classical.choice` with `#print axioms _`
theorem exercise_2_2_classical (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  intro pq nq p
  have := Classical.em Q
  rcases this with (q | nq)
  · exact nq q
  · exact nq (pq p)

#print axioms exercise_2_2_classical -- propext, Classical.choice, Quot.sound

#golf theorem exercise_2_2_classical' (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  intro h nq
  by_cases p : P
  · exfalso; exact nq (h p)
  · exact p

#print axioms exercise_2_2_classical' -- propext, Classical.choice, Quot.sound


-- A neat notational trick: `‹P›` looks for any proof of `P` in your assumptions
#golf theorem exercise_2_2_classical'' (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  intro _ _
  by_cases P
  · exfalso; exact ‹¬Q› (‹P → Q› ‹P›)
  · exact ‹¬P›

-- `by_contra` is intelligent about not applying `Classical.em` when applied to `¬P`
theorem exercise_2_2_not_quite_classical (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  intro pq nq
  by_contra p
  let h := pq p
  contradiction

#print axioms exercise_2_2_not_quite_classical -- no axioms used

/-
## Exercise Block B03
-/

-- Exercise 3.1
example (P Q : Prop) : (P → Q) ↔ (¬Q → ¬P) := by
  sorry

-- Exercise 3.2
-- Prove this using a case distinction on `P`
example (P Q : Prop) : (P → Q) → (¬P → Q) → Q := by
  sorry

-- Exercise 3.3 (Master)
-- Prove this by combining `by_cases` with `push_neg`
example (P : Prop) : ¬(P ↔ ¬P) := by
  sorry

-- Exercise 3.4 (Master)
-- Prove this using as few characters as possible
example (A B C : Prop) : (A ∧ (¬¬C)) ∨ (¬¬B) ∧ C ↔ (A ∧ C) ∨ B ∧ (¬¬C) := by
  sorry
