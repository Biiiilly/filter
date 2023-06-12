/-
Copyright (c) 2023 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Yichen Feng, Lily Frost, Archie Prime
Thanks: Kevin Buzzard
-/

import order.copy

/-!
# Filters

We define the filters and some basic properties of the filters in this file.
Notice: there is no puzzle in this file, and please read the instruction before
starting playing game.

# Main Definitions

`filter` : A filter is a collection of subsets which contains the whole set, upward closed
and closed under intersection.

-/

open set

-- Firstly, let's define the filters:
/-- A filter is a collection of subsets which contains the whole set, upward closed
and closed under intersection. -/
structure filter (α : Type*) :=
(sets                     : set (set α))
(univ_sets                : set.univ ∈ sets)
(upward_closure {F₁ F₂}   : F₁ ∈ sets → F₁ ⊆ F₂ → F₂ ∈ sets)
(inter_sets {F₁ F₂}       : F₁ ∈ sets → F₂ ∈ sets → F₁ ∩ F₂ ∈ sets)

namespace filter

-- Say f and g are two filters, and s t are two subsets of α. 
variables {α : Type*} {f g : filter α} {s t : set α}

-- A filter f is a collection of subsets, 
-- so clearly we want to do something like (s : set α) ∈ (f : filter α). 
instance : has_mem (set α) (filter α) := ⟨λ U F, U ∈ F.sets⟩

@[simp] lemma mem_sets : s ∈ f.sets ↔ s ∈ f := iff.rfl

lemma filter_eq : ∀ {f g : filter α}, f.sets = g.sets → f = g
| ⟨a, _, _, _⟩ ⟨._, _, _, _⟩ rfl := rfl

-- two filters are equal if and only if they contain the same sets.
lemma filter_eq_iff : f = g ↔ f.sets = g.sets :=
⟨congr_arg _, filter_eq⟩

lemma ext_iff : f = g ↔ ∀ s, s ∈ f ↔ s ∈ g :=
by simp only [filter_eq_iff, ext_iff, filter.mem_sets]

@[ext]
lemma ext : (∀ s, s ∈ f ↔ s ∈ g) → f = g :=
filter.ext_iff.2

-- The following three lemmas are directlyfrom the definiton of the filters:
@[simp] lemma univ_mem : univ ∈ f :=
f.univ_sets

lemma mem_of_superset {x y : set α} (hx : x ∈ f) (hxy : x ⊆ y) : y ∈ f :=
f.upward_closure hx hxy

lemma inter_mem {s t : set α} (hs : s ∈ f) (ht : t ∈ f) : s ∩ t ∈ f :=
f.inter_sets hs ht

end filter
