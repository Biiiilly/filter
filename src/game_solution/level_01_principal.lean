/-
Copyright (c) 2023 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Yichen Feng, Lily Frost, Archie Prime
Thanks: Kevin Buzzard
-/

import game_solution.level_01_basis

/-!
# Principal filters



# Main Definitions



-/

open set

variables {α : Type*}

namespace filter

/-- The principal filter of `s` is the collection of all supersets of `s`. -/
def principal (s : set α) : filter α :=
{ sets             := {t | s ⊆ t},
  univ_sets        := subset_univ s,
  upward_closure   := λ x y hx, subset.trans hx,
  inter_sets       := λ x y, subset_inter }

notation `𝓟` := filter.principal

@[simp] lemma mem_principal {s t : set α} : s ∈ 𝓟 t ↔ t ⊆ s := iff.rfl

lemma mem_principal_self (s : set α) : s ∈ 𝓟 s := subset.rfl

lemma le_principal_iff {s : set α} {f : filter α} : f ≤ 𝓟 s ↔ s ∈ f :=
begin
  split,
  { intro h,
    exact h (mem_principal_self s) },
  { intros h u hu,
    rw mem_principal at hu,
    exact mem_of_superset h hu }
end

lemma principal_mono {s t : set α} : 𝓟 s ≤ 𝓟 t ↔ s ⊆ t :=
  by simp only [le_principal_iff, mem_principal, imp_self]

@[simp] lemma principal_eq_iff_eq {s t : set α} : 𝓟 s = 𝓟 t ↔ s = t :=
  by by simp only [le_antisymm_iff, le_principal_iff, mem_principal]; refl

instance : order_top (filter α) :=
{ top    := { sets            := {s | ∀ x, x ∈ s},
              univ_sets        := λ x, mem_univ x,
              upward_closure   := λ x y hx hxy a, hxy (hx a),
              inter_sets       := λ x y hx hy a, mem_inter (hx _) (hy _) },
  le_top := 
  begin
    intros f u hu,
    suffices : u = univ,
    { rw this,
      exact univ_mem },
    change ∀ x, x ∈ u at hu,
    rwa ← eq_univ_iff_forall at hu, 
  end }

lemma mem_top_iff_forall {s : set α} : s ∈ (⊤ : filter α) ↔ (∀ x, x ∈ s) :=
iff.rfl

@[simp] lemma mem_top {s : set α} : s ∈ (⊤ : filter α) ↔ s = univ :=
by rw [mem_top_iff_forall, eq_univ_iff_forall]

@[simp] lemma principal_univ : 𝓟 (univ : set α) = ⊤ :=
begin
  apply top_unique,
  simp only [le_principal_iff, mem_top, eq_self_iff_true],
end

instance : has_bot (filter α) :=
⟨{ sets            := univ,
  univ_sets        := by simp only [mem_univ],
  upward_closure   := by simp only [mem_univ, implies_true_iff, forall_const],
  inter_sets       := by simp only [mem_univ, forall_const]}⟩

instance : order_bot (filter α) :=
{ bot := { sets             := univ,
           univ_sets        := by simp only [mem_univ],
           upward_closure   := by simp only [mem_univ, implies_true_iff, forall_const],
           inter_sets       := by simp only [mem_univ, forall_const]},
  bot_le :=  
  begin
    intros f u hu,
    exact mem_univ u,
  end }

@[simp] lemma principal_empty : 𝓟 (∅ : set α) = ⊥ :=
begin
  apply bot_unique,
  intros s hs,
  exact empty_subset s,
end

end filter