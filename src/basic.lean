import tactic

structure filter (X : Type*) :=
(sets                     : set (set X))
(upward_closure {F₁ F₂}   : F₁ ∈ sets → F₁ ⊆ F₂ → F₂ ∈ sets)
(inter_sets {F₁ F₂}       : F₁ ∈ sets → F₂ ∈ sets → F₁ ∩ F₂ ∈ sets)

instance {X : Type*}: has_mem (set X) (filter X) := ⟨λ U F, U ∈ F.sets⟩

namespace filter


end filter