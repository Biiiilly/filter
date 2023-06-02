import tactic

open function set order

-- Definition 2.1
structure filter (X : Type*) :=
(sets                     : set (set X))
(upward_closure {F₁ F₂}   : F₁ ∈ sets → F₁ ⊆ F₂ → F₂ ∈ sets)
(inter_sets {F₁ F₂}       : F₁ ∈ sets → F₂ ∈ sets → F₁ ∩ F₂ ∈ sets)

variables {X : Type*} {f g : filter X} {s : set X}
namespace filter

instance : has_mem (set X) (filter X) := ⟨λ U F, U ∈ F.sets⟩

@[simp] lemma mem_sets : s ∈ f.sets ↔ s ∈ f := iff.rfl

lemma filter_eq : ∀ {f g : filter X}, f.sets = g.sets → f = g
| ⟨a, _, _⟩ ⟨._, _, _⟩ rfl := rfl

lemma filter_eq_iff : f = g ↔ f.sets = g.sets :=
⟨congr_arg _, filter_eq⟩

protected lemma ext_iff : f = g ↔ ∀ s, s ∈ f ↔ s ∈ g :=
by simp only [filter_eq_iff, ext_iff, filter.mem_sets]

@[ext]
protected lemma ext : (∀ s, s ∈ f ↔ s ∈ g) → f = g :=
filter.ext_iff.2

end filter

-- Definition 2.2
structure filter_basis (X : Type*) :=
(sets                   : set (set X))
(inter_sets {x y}       : x ∈ sets → y ∈ sets → ∃ z ∈ sets, z ⊆ x ∩ y)
--(nonempty               : sets.nonempty)

instance {X : Type*} : has_mem (set X) (filter_basis X) := sorry

-- Definition 2.2
def filter_basis.filter (B : filter_basis X) : filter X :=
{ sets := {s | ∃ t ∈ B, t ⊆ s},
  upward_closure := sorry,
  inter_sets := sorry, }

namespace filter

-- Prop 2.3
def as_basis (f : filter X) : filter_basis X :=
⟨f.sets, sorry⟩

-- Prop 2.4
lemma generated_filter_eq (h : filter_basis.filter (filter.as_basis f) = g) : 
  f = g := sorry


end filter

