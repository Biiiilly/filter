/-
Copyright (c) 2023 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Yichen Feng, Lily Frost, Archie Prime
Thanks: Kevin Buzzard
-/

import game.level_03_principal


/-!
# Challenging Puzzles

This level contains some challenging puzzles. Notice that some of the lemmas or theorems
below are used in the previous levels.

-/

open set

variables {α : Type*}

namespace filter

/--
The infimum of filters is the filter generated by intersections of elements 
of the two filters.
-/
instance : has_inf (filter α) := ⟨λf g : filter α,
{ sets             := {s | ∃ (a ∈ f) (b ∈ g), s = a ∩ b },
  univ_sets        := 
  begin
    sorry 
  end,
  upward_closure   := 
  begin
    sorry
  end,
  inter_sets       :=
  begin
    sorry
  end }⟩

lemma mem_inf_iff {f g : filter α} {s : set α} :
  s ∈ f ⊓ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, s = t₁ ∩ t₂ := iff.rfl

lemma inter_mem_inf {f g : filter α} {s t : set α}
  (hs : s ∈ f) (ht : t ∈ g) : s ∩ t ∈ f ⊓ g :=
begin
  sorry
end

/-
Now we are coming to another challenging puzzle.
Hint for the forward direction: 'mem_inf_iff'
Hint for the backward direction: 'inter_mem_inf' and consider 's ∩ t'
-/
theorem mem_inf_principal {f : filter α} {s t : set α} :
  s ∈ f ⊓ 𝓟 t ↔ {x | x ∈ t → x ∈ s} ∈ f :=
begin
  sorry
end

-- Hint: 'filter.inter_mem' might be helpful.
lemma compl_not_mem {f : filter α} {s : set α} (hf : f ≠ ⊥) (h : s ∈ f) : sᶜ ∉ f :=
begin
  sorry
end

instance : semilattice_inf (filter α) :=
{ inf := filter.has_inf.inf,
  le := filter.partial_order.le,
  le_refl := partial_order.le_refl,
  le_trans := partial_order.le_trans,
  le_antisymm := partial_order.le_antisymm,
  inf_le_left :=
  begin
    sorry
  end,
  inf_le_right :=
  begin
    sorry
  end,
  le_inf :=
  begin
    sorry
  end }

end filter
