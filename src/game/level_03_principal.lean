/-
Copyright (c) 2023 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Yichen Feng, Lily Frost, Archie Prime
Thanks: Kevin Buzzard
-/

import game.level_02_order

/-!
# Principal filters

We define the principal filters in this file.

# Main Definitions

`principal` : The principal filter of `s` is the collection of all supersets of `s`.

-/

open set

variables {α : Type*} {s : set α}

namespace filter

-- Firstly, let's define the principal filters:
/-- The principal filter of `s` is the collection of all supersets of `s`. -/
def principal (s : set α) : filter α :=
{ sets             := {t | s ⊆ t},
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
  end }

-- We denote the principal filters as '𝓟' for convenience:
notation `𝓟` := filter.principal

#check 𝓟 s -- represents the principal filter of s

@[simp] lemma mem_principal {s t : set α} : s ∈ 𝓟 t ↔ t ⊆ s := iff.rfl

lemma mem_principal_self (s : set α) : s ∈ 𝓟 s := subset.rfl

/-- A filter f is finer than the principal filter of s if and only if s ∈ f. -/
lemma le_principal_iff {s : set α} {f : filter α} : f ≤ 𝓟 s ↔ s ∈ f :=
begin
  sorry
end

/-- The principal filter of s is finer than the principal filter of t 
if and only if s ⊆ t. -/
lemma principal_mono {s t : set α} : 𝓟 s ≤ 𝓟 t ↔ s ⊆ t :=
begin
  sorry
end

/-- The principal filter of s is equal to the principal filter of t 
if and only if s = t. -/
@[simp] lemma principal_eq_iff_eq {s t : set α} : 𝓟 s = 𝓟 t ↔ s = t :=
begin
  sorry
end

section order_filter

/--
Next, our goal: Prove '𝓟 (univ : set α) = ⊤' and '𝓟 (∅ : set α) = ⊥'
Before we go to these,
we firstly want to consider how to define the top (⊤) and the bottom (⊥) of filters.
i.e. the largest filter and the smallest filter
Remark: 
When we say that a filter f ≤ filter g , 
it means that g ⊆ f. i.e. ∀ s ∈ g → s ∈ f
Idea: 
The smallest filter corresponds to the finest one, so it should contain every subset.
Similarly, the largest filter should only contain the whole set.
-/

-- Let's verify these:
instance : order_top (filter α) :=
{ top    := { sets             := {s | ∀ x, x ∈ s},
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
              end },
  le_top := 
  begin
    sorry
  end }

lemma mem_top_iff_forall {s : set α} : s ∈ (⊤ : filter α) ↔ (∀ x, x ∈ s) :=
iff.rfl

@[simp] lemma mem_top {s : set α} : s ∈ (⊤ : filter α) ↔ s = univ :=
begin
  sorry
end

-- Hint: consider the magic of 'simp'
instance : order_bot (filter α) :=
{ bot := { sets             := univ,
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
           end },
  bot_le :=  
  begin
    sorry
  end }

end order_filter

@[simp] lemma mem_bot {s : set α} : s ∈ (⊥ : filter α) :=
trivial

lemma empty_mem_iff_bot {f : filter α} : ∅ ∈ f ↔ f = ⊥ :=
begin
  sorry
end

-- Hint: 'top_unique' is a good start.
@[simp] lemma principal_univ : 𝓟 (univ : set α) = ⊤ :=
begin
  sorry
end

-- Hint: can you guess this hint using the above hint?
@[simp] lemma principal_empty : 𝓟 (∅ : set α) = ⊥ :=
begin
  sorry
end

end filter
