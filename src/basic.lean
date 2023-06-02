import tactic

-- Definition 2.1
structure filter (X : Type*) :=
(sets                     : set (set X))
(upward_closure {F₁ F₂}   : F₁ ∈ sets → F₁ ⊆ F₂ → F₂ ∈ sets)
(inter_sets {F₁ F₂}       : F₁ ∈ sets → F₂ ∈ sets → F₁ ∩ F₂ ∈ sets)

instance {X : Type*} : has_mem (set X) (filter X) := ⟨λ U F, U ∈ F.sets⟩

variables {X : Type*} {f g : filter X} {s : set X}

@[simp] lemma filter.mem_sets : s ∈ f.sets ↔ s ∈ f := iff.rfl

-- Definition 2.2
structure filter_basis (X : Type*) :=
(sets                   : set (set X))
(inter_sets {x y}       : x ∈ sets → y ∈ sets → ∃ z ∈ sets, z ⊆ x ∩ y)
--(nonempty               : sets.nonempty)

instance {X : Type*} : has_mem (set X) (filter_basis X) := sorry

protected def filter_basis.filter (B : filter_basis X) : filter X :=
{ sets := {s | ∃ t ∈ B, t ⊆ s},
  upward_closure := sorry,
  inter_sets := sorry, }

-- Prop 2.3
def filter.as_basis (f : filter X) : filter_basis X :=
⟨f.sets, sorry⟩

-- Prop 2.4

