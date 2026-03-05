---
title: "Measuring proof length"
parent: Addendum
nav_order: 9996
---

# Measuring proof length
{: .no_toc }

*March 4, 2026 · `P02.S03.B02`*

---

In the exercise blocks we asked you to minimize the number of non-whitespace characters in your proof. The [`ProofGolf`](https://github.com/FordUniver/ProofGolf) package provides a `#golf` command that measures this automatically.

## Adding `ProofGolf` to your project

Add the dependency to your `lakefile.toml`:

```toml
[[require]]
name = "ProofGolf"
git = "https://github.com/FordUniver/ProofGolf"
rev = "main"
```

Then run `lake update ProofGolf` and add `import ProofGolf` at the top of any file where you want to use it.

## Usage

Wrap any declaration with `#golf`:

```lean
#golf example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro ⟨p, q⟩
  exact ⟨q, p⟩
-- Golf: 20 chars | term: 25 nodes | pp: 30 chars | axioms: none
```

For named declarations, `#golf` also reports the elaborated proof term size, pretty-printed length, and which foundational axioms the proof depends on:

```lean
#golf theorem em (P : Prop) : P ∨ ¬P := by exact Classical.em P
-- Golf: 18 chars | term: 5 nodes | pp: 23 chars | axioms: 3 (Classical.choice, propext, Quot.sound)
```

## Scoring rules

Whitespace is free: indentation and newlines do not count. The tactic separator `;` is also free since it is equivalent to a newline, so formatting choices do not affect your score. The tactic combinator `<;>`, which applies a tactic to all remaining goals, **does** count.

## How it works

`#golf` is a custom Lean 4 elaboration command. It wraps any declaration (`example`, `theorem`, `def`), elaborates it normally, then extracts the proof body from the syntax tree using source positions. For term-level metrics, it looks up the elaborated proof term in the environment (for `example` declarations, it re-elaborates a synthetic `def` to capture the term). Axiom dependencies are collected transitively using Lean's built-in `collectAxioms`.
