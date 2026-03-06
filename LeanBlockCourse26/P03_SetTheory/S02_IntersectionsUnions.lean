/-
This section is mostly inspired by the Set Theory Game:
https://github.com/leanprover-community/lean4game
-/

import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.NthRewrite
import LeanBlockCourse26.P03_SetTheory.S01_SubsetsComplements

variable {α : Type*}

/-
# Sets: Intersections and Unions
=====================

## Intersection Basics

The intersection of two sets `S` and `T`, denoted `S ∩ T`, is defined as the
set of elements `x` for which `x ∈ S ∧ x ∈ T`.
-/

example (S T : Set α) : S ∩ T = {x | x ∈ S ∧ x ∈ T} := rfl

theorem mem_inter_iff (x : α) (S T : Set α) : x ∈ S ∩ T ↔ x ∈ S ∧ x ∈ T := by
  rfl

#check Set.mem_inter_iff

theorem mem_of_mem_inter_right {x : α} {S T : Set α} (h : x ∈ S ∩ T) : x ∈ T := by
  rw [mem_inter_iff] at h -- optional because we are just rewriting with equal definition
  exact h.2

example {x : α} {S T : Set α} (h : x ∈ S ∩ T) : x ∈ T := h.2

theorem inter_subset_left (S T : Set α) : S ∩ T ⊆ S := by
  rw [subset_def]
  intro x h
  rw [mem_inter_iff] at h
  exact h.left

example (S T : Set α) : S ∩ T ⊆ S :=
  fun _ h => h.left

theorem mem_inter {x : α} {S T : Set α} (h₁ : x ∈ S) (h₂ : x ∈ T) : x ∈ S ∩ T := by
  rw [mem_inter_iff]
  constructor
  all_goals assumption

example {x : α} {S T : Set α} (h₁ : x ∈ S) (h₂ : x ∈ T) : x ∈ S ∩ T := ⟨h₁, h₂⟩

/-
## Exercise Block B01
-/

namespace P03S02B01

variable (S T : Set α)

-- Exercise 1.1
theorem inter_subset_swap : S ∩ T ⊆ T ∩ S := by
  intro x ⟨xs, xt⟩
  constructor
  · exact xt
  · exact xs

example : S ∩ T ⊆ T ∩ S := by
  intro _ ⟨xs, xt⟩
  exact ⟨xt, xs⟩

example : S ∩ T ⊆ T ∩ S :=
  fun _ ⟨xs, xt⟩ => ⟨xt, xs⟩

example : S ∩ T ⊆ T ∩ S :=
  fun _ x => ⟨x.2, x.1⟩

-- Exercise 1.2
theorem subset_inter (R : Set α) (h₁ : R ⊆ S) (h₂ : R ⊆ T) : R ⊆ S ∩ T := by
  intro x xr
  rw [mem_inter_iff]
  exact ⟨h₁ xr, h₂ xr⟩

example (R : Set α) (h₁ : R ⊆ S) (h₂ : R ⊆ T) : R ⊆ S ∩ T :=
  fun _ xr => ⟨h₁ xr, h₂ xr⟩

-- Exercise 1.3
theorem inter_comm : S ∩ T = T ∩ S := by
  ext x
  constructor <;> intro h <;> exact ⟨h.2, h.1⟩

example : S ∩ T = T ∩ S := by
  ext x
  repeat rw [mem_inter_iff]
  exact And.comm

example : S ∩ T = T ∩ S := by
  apply Set.ext
  intro x
  exact And.comm

example : S ∩ T = T ∩ S :=
  Set.ext (fun _ => And.comm)

-- Exercise 1.4
theorem inter_assoc (R : Set α) : (R ∩ S) ∩ T = R ∩ (S ∩ T) := by
  ext x
  repeat rw [mem_inter_iff]
  exact and_assoc

example (R : Set α) : (R ∩ S) ∩ T = R ∩ (S ∩ T) :=
  Set.ext (fun _ => and_assoc)

-- Note the inconsistent default bracketing ...
example (R : Set α) :    R ∩ S ∩ T = (R ∩ S) ∩ T   := rfl
example (P Q R : Prop) : P ∧ Q ∧ R ↔ P ∧ (Q ∧ R)   := by rfl

end P03S02B01

/-
## Union Basics

The union of two sets `S` and `T`, denoted `S ∪ T`, is defined as the
set of elements `x` for which `x ∈ S ∨ x ∈ T`.
-/

theorem mem_union (x : α) (S T : Set α) : x ∈ S ∪ T ↔ x ∈ S ∨ x ∈ T := by rfl

/-
## Exercise Block B02
-/

namespace P03S02B02

variable (S T : Set α)

-- Exercise 2.1
theorem subset_union_right : T ⊆ S ∪ T := by
  intro x xt
  rw [Set.mem_union]
  right
  exact xt

example (S T : Set α) : T ⊆ S ∪ T := fun _ xt => Or.inr xt

-- Exercise 2.2
theorem union_subset (R : Set α) (h₁ : R ⊆ T) (h₂ : S ⊆ T) : R ∪ S ⊆ T := by
  rintro x (xr | xs)
  · exact h₁ xr
  · exact h₂ xs

example (R S T : Set α) (h₁ : R ⊆ T) (h₂ : S ⊆ T) : R ∪ S ⊆ T := by
  rintro x xrs
  rcases xrs with xr | xs
  · exact h₁ xr
  · exact h₂ xs

-- Exercise 2.3
theorem union_subset_swap : S ∪ T ⊆ T ∪ S := by
  intro x xst
  rw [mem_union] at *
  apply or_comm.mp 
  exact xst

example (S T : Set α) : S ∪ T ⊆ T ∪ S := by
  intro x xst
  rw [mem_union] at *
  rw [or_comm]
  exact xst

example (S T : Set α) : S ∪ T ⊆ T ∪ S :=
  fun _ xst => or_comm.mp xst

-- Exercise 2.4
theorem union_comm : S ∪ T = T ∪ S := by
  ext x
  rw [mem_union] -- this is optional
  exact or_comm

-- Exercise 2.5 (Master)
theorem compl_inter : (S ∩ T)ᶜ = Sᶜ ∪ Tᶜ := by
  ext x
  rw [mem_compl_iff, mem_inter_iff, mem_union, mem_compl_iff, mem_compl_iff]
  push_neg
  constructor
  · intro h
    by_cases xs : x ∈ S 
    · right; exact h xs
    · left; exact xs
  · intro h xs
    obtain (nxs | nxt) := h
    · contradiction
    · exact nxt

-- Exercise 2.6 (Master)
-- This very nice solutions is thanks to Silas!
theorem compl_union : (S ∪ T)ᶜ = Sᶜ ∩ Tᶜ := by
  nth_rw 1 [← compl_compl S, ← compl_compl T]
  rw [← compl_inter Sᶜ Tᶜ, compl_compl]

-- Exercise 2.7 (Master)
theorem union_assoc (R : Set α) : (R ∪ S) ∪ T = R ∪ (S ∪ T) := by
  ext x
  -- rw [mem_union, mem_union, mem_union, mem_union]
  exact or_assoc

-- Exercise 2.8 (Master)
theorem inter_distrib_left (R : Set α) : R ∩ (S ∪ T) = (R ∩ S) ∪ (R ∩ T) := by
  ext x
  -- rw [mem_union, mem_inter_iff, mem_union, mem_inter_iff, mem_inter_iff]
  exact and_or_left -- this is just `P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R)`

-- Exercise 2.9 (Master)
example (R S T : Set α) (h₁ : R ∪ T ⊆ S ∪ T) (h₂ : R ∩ T ⊆ S ∩ T) : R ⊆ S := by
  intro x xr
  have xrut : x ∈ R ∪ T := Or.inl xr
  have xsut : x ∈ S ∪ T := h₁ xrut
  obtain (xs | xt) := xsut
  · assumption
  · have xrit : x ∈ R ∩ T := ⟨xr, xt⟩
    have xsit : x ∈ S ∩ T := h₂ xrit
    obtain ⟨xs, xt⟩ := xsit
    assumption

example (R : Set α) (h₁ : R ∪ T ⊆ S ∪ T) (h₂ : R ∩ T ⊆ S ∩ T) : R ⊆ S := by
  intro x xr
  obtain (xs | xt) := h₁ (Or.inl xr)
  · exact xs
  · exact (h₂ ⟨xr, xt⟩).1

-- Finally, note the inconsistent naming scheme:
#check Set.mem_inter_iff  -- `x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b` has `_iff` suffix ...
#check Set.mem_union      -- ... `x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b` does not

end P03S02B02
