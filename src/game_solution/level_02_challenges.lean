/-
Copyright (c) 2023 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Yichen Feng, Lily Frost, Archie Prime
Thanks: Kevin Buzzard
-/

import game_solution.level_01_principal


/-!
# Principal filters



# Main Definitions



-/

open set

variables {α : Type*}

instance : has_inf (filter α) := ⟨λf g : filter α,
{ sets             := {s | ∃ (a ∈ f) (b ∈ g), s = a ∩ b },
  univ_sets        := sorry,
  upward_closure   := sorry,
  inter_sets       := sorry }⟩

/-
lemma eq_infi_principal (B : filter_basis α) : B.filter = ⨅ s : B.sets, 𝓟 s :=
begin
  sorry
end
-/