---
title: Quick Reference
parent: Cheat Sheets
nav_order: 1
---

# Quick Reference
{: .no_toc }

What tactic do I need? Find the connective in your **goal** or **hypothesis** and read across.

---

## Logical connectives

| | `⊢` Goal | Hypothesis `h` |
|---|---|---|
| **And** `P ∧ Q` | `constructor` / `exact ⟨p, q⟩` | `obtain ⟨p, q⟩ := h` / `h.1`, `h.2` |
| **Or** `P ∨ Q` | `left` / `right` | `rcases h with p \| q` |
| **Implication** `P → Q` | `intro p` | `apply h` / `exact h p` |
| **Negation** `¬P` | `intro p` (it is `P → False`) | `exact h p` / `contradiction` |
| **Equivalence** `P ↔ Q` | `constructor` | `rw [h]` / `h.mp`, `h.mpr` |
| **Inequality** `a ≠ b` | `intro h` (it is `a = b → False`) | `exact h rfl` / `contradiction` |

**`push_neg`** simplifies negated compound statements by pushing `¬` inward: `¬∀` becomes `∃ ¬`, `¬(P ∧ Q)` becomes `P → ¬Q`, and so on. Works on both goals (`push_neg`) and hypotheses (`push_neg at h`).

## Equality and arithmetic

| | `⊢` Goal | Hypothesis `h` |
|---|---|---|
| **Equality** `a = b` | `rfl` | `rw [h]` / `rw [← h]` |
{% comment %}
| **Equality** `a = b` | `rfl` / `calc` / `ring` / `omega` | `rw [h]` / `rw [← h]` |
| **Inequality** `a < b`, `a ≤ b` | `omega` / `linarith` | `omega` / `linarith` |
{% endcomment %}

Use `rw [h] at h'` to rewrite in a specific hypothesis. Use `nth_rw n [h]` to rewrite only the *n*-th occurrence.

## Quantifiers

| | `⊢` Goal | Hypothesis `h` |
|---|---|---|
| **Universal** `∀ x, P x` | `intro x` | `apply h` / `exact h a` |
| **Existential** `∃ x, P x` | `use a` | `obtain ⟨x, hx⟩ := h` |

{% comment %}
`choose f hf using h` extracts a witness function from `h : ∀ x, ∃ y, P x y`, yielding `f : X → Y` and `hf : ∀ x, P x (f x)`.
{% endcomment %}

## True, False, and closing tactics

| | `⊢` Goal | Hypothesis `h` |
|---|---|---|
| **True** | `trivial` | — |
| **False** | `exfalso` | `contradiction` |

When the goal matches a hypothesis exactly, `exact h` or `assumption` closes it.

## Tactic mode and term mode

Tactic mode (after `by`) builds proofs step by step. Term mode constructs proofs directly as expressions. You can mix both freely.

| Direction | Syntax | Example |
|---|---|---|
| Enter tactic mode | `by` | `theorem ... := by intro p; exact p` |
| Use a term in tactic mode | `exact` | `exact ⟨p, q⟩` |
| Use tactics inside a term | `by` in subexpression | `⟨p, by assumption⟩` |
| Term mode function | `fun x => ...` | `fun p => ⟨p, p⟩` |
| Anonymous constructor | `⟨...⟩` | `⟨h.2, h.1⟩` for `Q ∧ P` |
| Field access | `.1`, `.2`, `.mp`, `.mpr` | `h.2` for second component |
| Function application | `f x` or `f <| x` | `h₂ (h₁ p)` or `h₂ <| h₁ p` |
| Composition | `g ∘ f` | `h₃ ∘ h₂ ∘ h₁` |

## Proof structure

| Tactic | Effect |
|---|---|
| `have q := h p` | Forward step: derive a new fact from existing ones |
| `suffices p : P by ...` | Backward step: state what would be enough, then prove it |
| `rintro ⟨p, q⟩` / `rintro (p \| q)` | Combine `intro` with pattern matching |
{% comment %}
| `calc a = b := ... _ = c := ...` | Chain equalities or inequalities through intermediate steps |
| `by_contra h` | Assume `¬ goal` and derive `False` (classical) |
| `by_cases h : P` | Split into `P` and `¬P` branches (classical) |
| `contrapose` | Flip `P → Q` to `¬Q → ¬P` (`contrapose!` also applies `push_neg`) |
| `induction n with \| zero => ... \| succ n ih => ...` | Structural induction on natural numbers or inductive types |
| `ext x` | Prove `f = g` by showing `∀ x, f x = g x` (functions, sets, etc.) |
{% endcomment %}

{% comment %}
## Automation

| Tactic | Proves |
|---|---|
| `simp` | Goals reducible by rewrite lemmas (`simp only [...]` for control) |
| `tauto` | Propositional tautologies |
| `omega` | Linear integer and natural number arithmetic |
| `linarith` | Linear arithmetic over ordered fields |
| `ring` | Polynomial identities in commutative (semi)rings |
| `norm_num` | Closed numerical expressions |
| `grind` | Mixed reasoning (congruence, arithmetic, quantifiers) |
| `decide` | Decidable propositions by computation (e.g., `2 + 3 = 5`) |
| `exact?` / `apply?` | Search the library for a matching lemma |
{% endcomment %}
