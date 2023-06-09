import tactic

open function set order

-- Definition 2.1
structure my_filter (X : Type*) :=
(sets                     : set (set X))
(upward_closure {F₁ F₂}   : F₁ ∈ sets → F₁ ⊆ F₂ → F₂ ∈ sets)
(inter_sets {F₁ F₂}       : F₁ ∈ sets → F₂ ∈ sets → F₁ ∩ F₂ ∈ sets)

variables {X : Type*} {f g : my_filter X} {s : set X}
namespace my_filter

instance : has_mem (set X) (my_filter X) := ⟨λ U F, U ∈ F.sets⟩

@[simp] lemma mem_sets : s ∈ f.sets ↔ s ∈ f := iff.rfl

lemma my_filter_eq : ∀ {f g : my_filter X}, f.sets = g.sets → f = g
| ⟨a, _, _⟩ ⟨._, _, _⟩ rfl := rfl

lemma my_filter_eq_iff : f = g ↔ f.sets = g.sets :=
⟨congr_arg _, my_filter_eq⟩

protected lemma ext_iff : f = g ↔ ∀ s, s ∈ f ↔ s ∈ g :=
by simp only [my_filter_eq_iff, ext_iff, my_filter.mem_sets]

@[ext]
protected lemma ext : (∀ s, s ∈ f ↔ s ∈ g) → f = g :=
my_filter.ext_iff.2

end my_filter

-- Section 2.3
section my_filter_basis

-- Def 2.8
structure my_filter_basis (X : Type*) :=
(sets                   : set (set X))
(inter_sets {x y}       : x ∈ sets → y ∈ sets → ∃ z ∈ sets, z ⊆ x ∩ y)


instance {X : Type*} : has_mem (set X) (my_filter_basis X) := sorry

-- Def 2.8
def my_filter_basis.my_filter (B : my_filter_basis X) : my_filter X :=
{ sets := {s | ∃ t ∈ B, t ⊆ s},
  upward_closure := sorry,
  inter_sets := sorry, }

namespace my_filter

-- Prop 2.9
def as_basis (f : my_filter X) : my_filter_basis X :=
⟨f.sets, sorry⟩

-- Prop 2.10
lemma generated_my_filter_eq (h : my_filter_basis.my_filter (my_filter.as_basis f) = g) : 
  f = g := sorry


end my_filter
end my_filter_basis

