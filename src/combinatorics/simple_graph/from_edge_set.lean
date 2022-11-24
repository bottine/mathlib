import combinatorics.simple_graph.basic
import data.set.finite
import data.sym.sym2

universes u v w

namespace simple_graph

variable (V : Type*)

@[simp] lemma from_edge_set_inf (s t : set (sym2 V)) :
  from_edge_set (s ∩ t) = from_edge_set s ⊓ from_edge_set t :=
by { ext v w, simp only [from_edge_set_adj, set.mem_inter_iff, ne.def, inf_adj], tauto, }

@[simp] lemma from_edge_set_sup (s t : set (sym2 V)) :
  from_edge_set (s ∪ t) = from_edge_set s ⊔ from_edge_set t :=
by { ext v w, simp [set.mem_union, or_and_distrib_right], }

@[simp] lemma from_edge_set_sdiff (s t : set (sym2 V)) :
  from_edge_set (s \ t) = from_edge_set s \ from_edge_set t :=
by { ext v w, split; simp { contextual := tt }, }

lemma from_edge_set_mono {s t : set (sym2 V)} (h : s ⊆ t) : from_edge_set s ≤ from_edge_set t :=
begin
  rintro v w,
  simp only [from_edge_set_adj, ne.def, not_false_iff, and_true, and_imp] {contextual := tt},
  exact λ vws _, h vws,
end

lemma from_edge_set_le_from_edge_set_iff {s t : set (sym2 V)} :
  from_edge_set s ≤ from_edge_set t ↔ (s \ (set_of sym2.is_diag)) ⊆ (t \ (set_of sym2.is_diag)) :=
begin
  split,
  { rintros h ⟨u,v⟩,
    change ⟦(u,v)⟧ ∈ s \ set_of sym2.is_diag → ⟦(u,v)⟧ ∈ t \ set_of sym2.is_diag,
    simp { contextual := tt },
    exact λ uvs ne, (h ⟨uvs,ne⟩).left, },
  { rintro h u v a, refine ⟨_,a.ne⟩,
    refine (h _).left, exact ⟨a.left,a.right⟩, },
end

lemma from_edge_set_eq_from_edge_set_iff {s t : set (sym2 V)} :
  from_edge_set s = from_edge_set t ↔ (s \ (set_of sym2.is_diag)) = (t \ (set_of sym2.is_diag)) :=
by simp [le_antisymm_iff, from_edge_set_le_from_edge_set_iff]

lemma le_from_edge_set_iff  (s : set (sym2 V)) (G : simple_graph V) :
  G ≤ from_edge_set s ↔ G.edge_set ⊆ s :=
begin
  split,
  { rintro h ⟨u,v⟩ a, exact (h a).left, },
  { rintro h u v a, refine ⟨h _, a.ne⟩, exact a,},
end

lemma from_edge_set_le_iff (s : set (sym2 V)) (G : simple_graph V) :
  from_edge_set s ≤ G ↔ (s \ (set_of sym2.is_diag)) ⊆ G.edge_set :=
begin
  nth_rewrite 0 ←from_edge_set_edge_set G,
  rw from_edge_set_le_from_edge_set_iff,
  have : G.edge_set \ set_of sym2.is_diag = G.edge_set, by
  { ext ⟨u,v⟩, simp only [set.mem_diff, set.mem_set_of_eq, and_iff_left_iff_imp], exact adj.ne, },
  rw this,
end

end simple_graph
