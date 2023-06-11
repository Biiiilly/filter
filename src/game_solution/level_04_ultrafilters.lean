/-
Copyright (c) 2023 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Yichen Feng, Lily Frost, Archie Prime
Thanks: Kevin Buzzard
-/

import game_solution.level_03_principal

/-!
# ultrafilters

We define the ultrafilters in this file.

# Main Definitions

`ultrafilter` : the ultrafiler

-/

open set

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


@[simp] lemma compl_not_mem_iff : sᶜ ∉ f ↔ s ∈ f :=
begin
  sorry
end

lemma compl_mem_iff_not_mem : sᶜ ∈ f ↔ s ∉ f := 
  by rw [← compl_not_mem_iff, compl_compl]

lemma diff_mem_iff (f : ultrafilter α) : s \ t ∈ f ↔ s ∈ f ∧ t ∉ f :=
begin
  sorry
end

/-- If `sᶜ ∉ f ↔ s ∈ f`, then `f` is an ultrafilter. The other implication is given by
`ultrafilter.compl_not_mem_iff`.  -/
def of_compl_not_mem_iff (f : filter α) (h : ∀ s, sᶜ ∉ f ↔ s ∈ f) : ultrafilter α :=
{ to_filter := f,
  ne_bot' := sorry,
  le_of_le := sorry }

end ultrafilter