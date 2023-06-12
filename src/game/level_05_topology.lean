/-
Copyright (c) 2023 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Yichen Feng, Lily Frost, Archie Prime
Thanks: Kevin Buzzard
-/

import game.level_04_ultrafilters


/-!
# Filters in topology

One of the applications of filters is about topology, and we will go
through some of them in this level.

-/

open set

/- The section below reviews basic knowledge of topological space. This is
basically from mathlib. Notice there is nothing to do in this section -/

section topology_review

universe u
variables {α : Type u} {a : α} {s s₁ s₂ : set α}

/-- A topology on `α`. -/
@[protect_proj] class topological_space (α : Type u) :=
(is_open        : set α → Prop)
(is_open_univ   : is_open univ)
(is_open_inter  : ∀s t, is_open s → is_open t → is_open (s ∩ t))
(is_open_sUnion : ∀s, (∀t∈s, is_open t) → is_open (⋃₀ s))

/-- A constructor for topologies by specifying the closed sets,
and showing that they satisfy the appropriate conditions. -/
def topological_space.of_closed {α : Type u} (T : set (set α))
  (empty_mem : ∅ ∈ T) (sInter_mem : ∀ A ⊆ T, ⋂₀ A ∈ T) (union_mem : ∀ A B ∈ T, A ∪ B ∈ T) :
  topological_space α :=
{ is_open := λ X, Xᶜ ∈ T,
  is_open_univ := by simp [empty_mem],
  is_open_inter := λ s t hs ht, by simpa only [compl_inter] using union_mem sᶜ hs tᶜ ht,
  is_open_sUnion := λ s hs,
    by rw set.compl_sUnion; exact sInter_mem (compl '' s)
    (λ z ⟨y, hy, hz⟩, by simpa [hz.symm] using hs y hy) }

variable [topological_space α]

/-- `is_open s` means that `s` is open in the ambient topological space on `α` -/
def is_open [topological_space α] (s : set α) : Prop := @topological_space.is_open _ ‹_› s

lemma is_open.inter (h₁ : is_open s₁) (h₂ : is_open s₂) : is_open (s₁ ∩ s₂) :=
topological_space.is_open_inter s₁ s₂ h₁ h₂

end topology_review

-- Now, coming to the main part of this level:

variables {α : Type*} [topological_space α] (a : α)

-- Firstly, let's define the neighbourhood filters 𝓝 a:
/-- A set is called a neighborhood of `a` if it contains an open set around `a`. The set of all
neighborhoods of `a` forms a filter, the neighborhood filter at `a`, denoted as 𝓝 a. -/
def nhds (a : α) : filter α :=
{ sets := {s : set α | ∃ t ⊆ s, is_open t ∧ a ∈ t},
  univ_sets := 
  begin
    sorry
  end,
  upward_closure :=
  begin
    sorry
  end,
  inter_sets :=
  begin
    sorry
  end }

notation `𝓝` := nhds

#check 𝓝 a

@[simp] lemma mem_nhds {s : set α} : s ∈ (𝓝 a) ↔ (∃ t ⊆ s, is_open t ∧ a ∈ t) := iff.rfl

-- Try these exercises below:
/-- To show a filter is above the neighborhood filter at `a`, it suffices to show that 
it is above the principal filter of some open set `s` containing `a`. -/
lemma nhds_le_of_le {f a} {s : set α} (h : a ∈ s) (ho : is_open s) (hsf : 𝓟 s ≤ f) : 
  (𝓝 a) ≤ f :=
begin
  sorry
end

lemma mem_of_mem_nhds {a : α} {s : set α} : s ∈ (𝓝 a) → a ∈ s :=
begin
  sorry
end

lemma is_open.mem_nhds {a : α} {s : set α} (hs : is_open s) (ha : a ∈ s) :
  s ∈ 𝓝 a :=
begin
  sorry
end

-- Using results above, we can get this:
lemma is_open.mem_nhds_iff {a : α} {s : set α} (hs : is_open s) : s ∈ (𝓝 a) ↔ a ∈ s :=
begin
  sorry
end
