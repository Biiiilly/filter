import order.filter.basic
import order.filter.bases

variables {X : Type*} {f g : filter X} {s : set X}

lemma filter.le_generate_le (f g : set (set X)) (h : f ≤ g) :
  filter.generate f ≤ filter.generate g :=
begin
  rw filter.sets_iff_generate,
  intros x hx,
  sorry
end

lemma filter.le_and_le_iff_generate_eq (f g : filter X):
  f ≤ g ∧ g ≤ f ↔ filter.generate f.sets = filter.generate g.sets :=
begin
  sorry
end