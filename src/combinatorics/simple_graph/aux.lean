import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.basic

open function

namespace simple_graph

variables {V : Type*} {G : simple_graph V} {u v : V}

section add_delete_edges

lemma delete_edges_eq_iff (s : set (sym2 V)) : G.delete_edges s = G ↔ disjoint s G.edge_set := sorry

lemma delete_edge_eq_iff (u v) :
  G.delete_edges {⟦⟨u,v⟩⟧} = G ↔ ¬ G.adj u v := by { simp [delete_edges_eq_iff] }

def add_edges (G : simple_graph V) (s : set (sym2 V)) : simple_graph V :=
{ adj := λ a b, G.adj a b ∨ (a ≠ b) ∧ sym2.to_rel s a b,
  symm := λ a b, by
  { rintro (l|⟨ne,r⟩),
    { exact or.inl l.symm, } ,
    { apply or.inr, exact ⟨ne.symm,(sym2.to_rel_symmetric s r)⟩ } },
  loopless := λ a, by
  { rintro (l|⟨ne,r⟩), { exact G.loopless a l, }, { exact ne rfl }, } }

def le_add_edges  (G : simple_graph V) (s : set (sym2 V)) : G ≤ (G.add_edges s) := by
{ rintros a b h, exact or.inl h, }

lemma add_edges_eq_iff (s : set (sym2 V)) :
  G.add_edges s = G ↔ (∀ u v, ((⟦⟨u,v⟩⟧ : sym2 V) ∈ s) → G.adj u v) := sorry

lemma add_edge_eq_iff (u v) (h : u ≠ v) : G.add_edges {⟦⟨u,v⟩⟧} = G ↔ G.adj u v :=
begin
  simp [add_edges_eq_iff],
  split,
  { rintros h', exact h' u v (by simp), },
  { rintro h' u v (⟨rfl,rfl⟩|⟨rfl,rfl⟩), exact h', exact h'.symm, },
end

lemma add_edge_adj (u v)  (h : u ≠ v) : (G.add_edges {⟦⟨u,v⟩⟧}).adj u v := sorry

lemma add_edge_hom_not_edges (u v) (h : u ≠ v)
  {x y : V} (p : G.path x y) :
  (⟦⟨u,v⟩⟧ : sym2 V) ∉
  ((simple_graph.path.map
    (simple_graph.hom.map_spanning_subgraphs (le_add_edges G {⟦⟨u,v⟩⟧}))
    (function.injective_id) p)).val.edges := sorry

lemma delete_edge_hom_not_edges (u v) (h : G.adj u v)
  {x y : V} (p : (G.delete_edges {⟦⟨u,v⟩⟧}).path x y) :
  (⟦⟨u,v⟩⟧ : sym2 V) ∉
  ((simple_graph.path.map
    (simple_graph.hom.map_spanning_subgraphs (delete_edges_le G {⟦⟨u,v⟩⟧}))
    (function.injective_id) p)).val.edges := sorry


end add_delete_edges


namespace path

lemma cons_is_cycle_iff {u v : V} (p : G.walk v u) (h : G.adj u v) :
  (p.cons h).is_cycle ↔ p.is_path ∧ ¬ ⟦(u, v)⟧ ∈ p.edges :=
begin
  split,
  { simp only [walk.is_cycle_def, walk.cons_is_trail_iff, ne.def, not_false_iff, walk.support_cons,
               list.tail_cons, true_and, simple_graph.walk.is_path_def],
    tauto, },
  { exact λ ⟨hp,he⟩, cons_is_cycle (⟨p,hp⟩ : G.path v u) h he, },
end

end path

namespace walk

abbreviation of_edge (e : G.adj u v) : G.walk u v := walk.cons e nil

abbreviation _root_.simple_graph.path.of_edge (e : G.adj u v) : G.path u v :=
⟨ walk.of_edge e, by
  { rw is_path_def,
    simp only [support_cons, support_nil, list.nodup_cons, list.mem_singleton,
               list.not_mem_nil, not_false_iff, list.nodup_nil, and_true],
    exact adj.ne e, } ⟩

variable (c : G.walk u u)

variables {V' : Type*} {G' : simple_graph V'} {f : G →g G'}

lemma map_is_cycle_of_injective (hinj : function.injective f) (hc : c.is_cycle) :
  (c.map f).is_cycle := sorry

protected lemma is_cycle.of_map {f : G →g G'} (hc : (c.map f).is_cycle) : c.is_cycle := sorry

lemma map_is_cycle_iff_of_injective (hinj : function.injective f) :
  (c.map f).is_cycle ↔ c.is_cycle := sorry

lemma split_along_set [decidable_eq V] :
∀ {u v : V} (p : G.walk u v) (S : set V) (uS : u ∈ S) (vS : v ∉ S),
  ∃ (x y : V) (w : G.walk u x) (a : G.adj x y) (w' : G.walk y v), p = w.append (cons a w') ∧  (w.support.to_finset : set V) ⊆ S ∧ y ∉ S
| _ _ nil p uS vnS := (vnS uS).elim
| _ _ (cons' u x v a w) S uS vnS := by
{ by_cases h : S x,
  { obtain ⟨x',y,w',a',w'',weq,wS,ynS⟩ := w.split_along_set S h vnS,
    use [x',y,cons a w',a',w''],
    split,
    { simp only [cons_append,weq], },
    { simp only [support_cons, list.to_finset_cons, finset.coe_insert, set.insert_subset],
      exact ⟨⟨uS,wS⟩,ynS⟩, }, },
  { use [u,x,nil,a,w],
    simp only [nil_append, eq_self_iff_true, support_nil, list.to_finset_cons,
               list.to_finset_nil, insert_emptyc_eq, finset.coe_singleton,
               set.singleton_subset_iff, true_and],
    exact ⟨uS,h⟩, }, }

lemma split_along_set' [decidable_eq V] :
∀ {u v : V} (p : G.walk u v) (S : set V) (uS : u ∈ S) (vS : v ∉ S),
  ∃ (x y : V), G.adj x y ∧ x ∈ S ∧ y ∉ S
| _ _ nil p uS vnS := (vnS uS).elim
| _ _ (cons' u x v a w) S uS vnS := by
{ by_cases h : S x,
  { exact w.split_along_set' S h vnS, },
  { exact ⟨u,x,a,uS,h⟩ }, }

end walk

end simple_graph
