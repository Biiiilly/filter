import topology.basic

-- Section 3.2
section nhds

universe u
variables {α : Type u} [topological_space α] (a : α)

-- Def 3.2 using lemma 3.3
def nhds_filter (a : α) : filter α :=
{ sets := {s : set α | a ∈ s},
  univ_sets := sorry,
  sets_of_superset := sorry,
  inter_sets := sorry }

local notation `𝓝[` a `] ` := nhds_filter a

#check 𝓝[a]



end nhds