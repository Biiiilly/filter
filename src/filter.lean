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

-- I will consider add this later after we define princpal filter.
-- Here is one challenging puzzle:
/-
lemma eq_infi_principal (B : filter_basis α) : B.filter = ⨅ s : B.sets, 𝓟 s :=
begin
  sorry
end
-/