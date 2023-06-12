/-
Copyright (c) 2023 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Yichen Feng, Lily Frost, Archie Prime
Thanks: Kevin Buzzard
-/

import game_solution.level_03_principal


/-!
# Challenging Puzzles

This file contains some challenging puzzles.

-/

open set

variables {α : Type*}

namespace filter

instance : has_inf (filter α) := ⟨λf g : filter α,
{ sets             := {s | ∃ (a ∈ f) (b ∈ g), s = a ∩ b },
  univ_sets        := sorry,
  upward_closure   := sorry,
  inter_sets       := sorry }⟩

lemma mem_inf_iff {f g : filter α} {s : set α} :
  s ∈ f ⊓ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, s = t₁ ∩ t₂ := iff.rfl

lemma inter_mem_inf {f g : filter α} {s t : set α}
  (hs : s ∈ f) (ht : t ∈ g) : s ∩ t ∈ f ⊓ g :=
⟨s, hs, t, ht, rfl⟩

theorem mem_inf_principal {f : filter α} {s t : set α} :
  s ∈ f ⊓ 𝓟 t ↔ {x | x ∈ t → x ∈ s} ∈ f :=
begin
  split,
  { intro hs,
    rw mem_inf_iff at hs,
    obtain ⟨u, hu, v, hv, huv⟩ := hs,
    subst huv,
    rw filter.mem_principal at hv,
    suffices : u ⊆ {x : α | x ∈ t → x ∈ u ∩ v},
    { exact mem_of_superset hu this },
    intros x hx,
    simp only [mem_inter_iff, mem_set_of_eq],
    intro hxt,
    refine ⟨hx, _⟩,
    exact hv hxt },
  { intro h,
    have goal : s ∪ tᶜ ∈ f, 
    { convert h,
      ext,
      simp only [mem_union, mem_compl_iff, mem_set_of_eq],
      rw imp_iff_not_or,
      rw or_comm },
    clear h,
    suffices : s ∩ t ∈ f ⊓ 𝓟 t,
    { have h : s ∩ t ⊆ s := by simp only [inter_subset_left],
      exact mem_of_superset this h,},
    have h₁ := inter_mem_inf goal (mem_principal_self t),
    rw set.union_inter_distrib_right at h₁,
    simp at h₁,
    exact h₁ }
end

lemma compl_not_mem {f : filter α} {s : set α} (hf : f ≠ ⊥) (h : s ∈ f) : sᶜ ∉ f :=
begin
  intro hsc,
  have hp : s ∩ sᶜ ∈ f := filter.inter_mem h hsc,
  rw inter_compl_self at hp,
  apply hf,
  rwa ← filter.empty_mem_iff_bot,
end

instance : semilattice_inf (filter α) :=
{ inf := filter.has_inf.inf,
  le := filter.partial_order.le,
  le_refl := sorry,
  le_trans := sorry,
  le_antisymm := sorry,
  inf_le_left := sorry,
  inf_le_right := sorry,
  le_inf := sorry }

/-
lemma eq_infi_principal (B : filter_basis α) : B.filter = ⨅ s : B.sets, 𝓟 s :=
begin
  sorry
end
-/

end filter