/-
Copyright (c) 2023 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Yichen Feng, Lily Frost, Archie Prime
Thanks: Kevin Buzzard
-/

import game_solution.level_03_principal
import game_solution.level_05_challenges

/-!
# ultrafilters

We define the ultrafilters in this file.

# Main Definitions

`ultrafilter` : the ultrafiler

-/

open set function

variable {α : Type*}

-- Firstly, let's define ultrafilers:
/-- An ultrafilter is a minimal (maximal in the set order) proper filter. -/
structure ultrafilter (α : Type*) :=
(to_filter : filter α)
(ne_bot'   : to_filter ≠ ⊥)
(le_of_le  : ∀ g, g ≠ ⊥ → g ≤ to_filter → to_filter ≤ g)

namespace ultrafilter

variables {f g : ultrafilter α} {s t : set α}

-- An ultrafilter is clearly a filter.
instance : has_coe_t (ultrafilter α) (filter α) := ⟨ultrafilter.to_filter⟩

instance : has_mem (set α) (ultrafilter α) := ⟨λ s f, s ∈ (f : filter α)⟩

-- If any filter g is finer than the ultrafilter f, then g = f,
-- since an ultrafilter is a minimal proper filter.
lemma unique (f : ultrafilter α) {g : filter α} (h : g ≤ f)
  (hne : g ≠ ⊥) : g = f :=
begin
  apply le_antisymm h,
  exact f.le_of_le g hne h,
end

@[simp, norm_cast] lemma mem_coe : s ∈ (f : filter α) ↔ s ∈ f := iff.rfl

lemma coe_injective : injective (coe : ultrafilter α → filter α)
| ⟨f, h₁, h₂⟩ ⟨g, h₃, h₄⟩ rfl := by congr

lemma eq_of_le {f g : ultrafilter α} (h : (f : filter α) ≤ g) : f = g :=
coe_injective (g.unique h f.ne_bot')

@[simp, norm_cast] lemma coe_le_coe {f g : ultrafilter α} : (f : filter α) ≤ g ↔ f = g :=
⟨λ h, eq_of_le h, λ h, h ▸ le_rfl⟩

@[simp, norm_cast] lemma coe_inj : (f : filter α) = g ↔ f = g := coe_injective.eq_iff

@[ext] lemma ext ⦃f g : ultrafilter α⦄ (h : ∀ s, s ∈ f ↔ s ∈ g) : f = g :=
coe_injective $ filter.ext h

lemma le_of_inf_ne_bot (f : ultrafilter α) {g : filter α} (hg : (↑f ⊓ g) ≠ ⊥) : 
  ↑f ≤ g :=
begin
  apply @le_of_inf_eq (filter α) _,
  apply unique f _ hg,
  exact inf_le_left,
end

lemma le_of_inf_ne_bot' (f : ultrafilter α) {g : filter α} (hg : (g ⊓ f) ≠ ⊥) : 
  ↑f ≤ g := f.le_of_inf_ne_bot $ by rwa inf_comm

lemma inf_ne_bot_iff {f : ultrafilter α} {g : filter α} : 
  (↑f ⊓ g) ≠ ⊥ ↔ ↑f ≤ g :=
begin
  split,
  { exact le_of_inf_ne_bot _ },
  { intro h,
    rw inf_of_le_left h,
    exact f.ne_bot' }
end

@[simp] lemma compl_not_mem_iff : sᶜ ∉ f ↔ s ∈ f :=
begin
  split,
  { intro h,
    rw ← mem_coe,
    rw ← filter.le_principal_iff,
    apply le_of_inf_ne_bot,
    intro h₁,
    rw ← filter.empty_mem_iff_bot at h₁,
    rw filter.mem_inf_principal at h₁,
    simp only [mem_empty_iff_false, mem_coe] at h₁,
    suffices : {x : α | x ∈ s → false} = sᶜ,
    { rw this at h₁,
      contradiction },
    ext,
    simp only [mem_set_of_eq],
    refl },
  { intro h,
    exact filter.compl_not_mem f.ne_bot' h }
end

lemma compl_mem_iff_not_mem : sᶜ ∈ f ↔ s ∉ f := 
  by rw [← compl_not_mem_iff, compl_compl]

/-- If `sᶜ ∉ f ↔ s ∈ f`, then `f` is an ultrafilter. The other implication is given by
`ultrafilter.compl_not_mem_iff`.  -/
def of_compl_not_mem_iff (f : filter α) (h : ∀ s, sᶜ ∉ f ↔ s ∈ f) : ultrafilter α :=
{ to_filter := f,
  ne_bot' := sorry,
  le_of_le := sorry }

end ultrafilter