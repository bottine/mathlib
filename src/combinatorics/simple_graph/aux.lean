import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.basic

open function

namespace simple_graph

variables {V : Type*} {G : simple_graph V} {u v : V}


namespace walk

lemma cons_is_cycle_iff {u v : V} (p : G.walk v u) (h : G.adj u v) :
  (p.cons h).is_cycle ↔ p.is_path ∧ ¬ ⟦(u, v)⟧ ∈ p.edges :=
begin
  split,
  { simp only [walk.is_cycle_def, walk.cons_is_trail_iff, ne.def, not_false_iff, walk.support_cons,
               list.tail_cons, true_and, simple_graph.walk.is_path_def],
    tauto, },
  { exact λ ⟨hp,he⟩, path.cons_is_cycle (⟨p,hp⟩ : G.path v u) h he, },
end

end walk

namespace walk

@[simp] def induce : Π {u v : V} (p : G.walk u v) {H : simple_graph V}
  (h : ∀ e, e ∈ p.edges → e ∈ H.edge_set), H.walk u v
| _ _ (walk.nil) H h := walk.nil
| _ _ (walk.cons a p) H h := by
  { refine walk.cons _ (p.induce _);
    simp only [walk.edges_cons, list.mem_cons_iff, forall_eq_or_imp, mem_edge_set] at h,
    exact h.1, exact h.2, }

variables (w : V) (p : G.walk u v)
  {H : simple_graph V} (h : ∀ e, e ∈ p.edges → e ∈ H.edge_set)

lemma induce_id : p.induce (λ e ep, edges_subset_edge_set p ep) = p := by
{ induction p,
  simp only [induce],
  simp only [p_ih, induce, eq_self_iff_true, heq_iff_eq, and_self], }

abbreviation induce_le (GH : G ≤ H) : H.walk u v :=
p.induce (λ e ep, edge_set_mono GH (edges_subset_edge_set p ep))

lemma induce_eq_map_spanning_subgraphs (GH : G ≤ H) :
  p.induce h = p.map (simple_graph.hom.map_spanning_subgraphs GH) := by
{ induction p,
  simp only [induce, map_nil],
  simp only [p_ih, induce, map_cons, hom.map_spanning_subgraphs_apply, eq_self_iff_true,
             heq_iff_eq, and_self], }

@[simp] lemma induce_edges : (p.induce h).edges = p.edges := by
{ induction p,
  simp only [induce, edges_nil],
  simp only [p_ih, induce, edges_cons, eq_self_iff_true, and_self], }

@[simp] lemma induce_support : (p.induce h).support = p.support := by
{ induction p,
  simp only [induce, support_nil, eq_self_iff_true, and_self],
  simp only [p_ih, induce, support_cons, eq_self_iff_true, and_self], }

lemma is_path_induce (hp : p.is_path) : (p.induce h).is_path := by
{ induction p,
  simp only [induce, is_path.nil],
  simp only [cons_is_path_iff, induce, induce_support] at hp ⊢,
  simp only [p_ih, hp, not_false_iff, and_self], }

def is_cycle_induce {u : V} (p : G.walk u u) {H : simple_graph V}
  (h : ∀ e, e ∈ p.edges → e ∈ H.edge_set) (hp : p.is_cycle) : (p.induce h).is_cycle := by
{ cases p,
  { simp only [induce, is_cycle.not_of_nil] at hp ⊢, exact hp, },
  { simp only [cons_is_cycle_iff, induce, induce_edges] at hp ⊢,
    refine ⟨_,hp.right⟩,
    apply is_path_induce,
    exact hp.left, }, }

abbreviation is_cycle_induce_le  {u : V} (p : G.walk u u) {H : simple_graph V}
  (GH : G ≤ H) (hp : p.is_cycle) :=
p.is_cycle_induce (λ e ep, edge_set_mono GH (edges_subset_edge_set p ep)) hp

lemma induce_comp {K : simple_graph V} (k : ∀ e, e ∈ p.edges → e ∈ K.edge_set) :
  (p.induce h).induce (by {rw p.induce_edges, exact k, }) = p.induce k := by
{ induction p,
  simp only [induce],
  simp only [induce, eq_self_iff_true, heq_iff_eq, true_and],
  apply p_ih, }

lemma induce_append (q : G.walk v w) (hq :  ∀ e, e ∈ q.edges → e ∈ H.edge_set) :
  (p.append q).induce (by { rintro e, simp, rintro (ep|eq), exact h e ep, exact hq e eq, }) =
  (p.induce h).append (q.induce hq) := by
{ induction p,
  simp only [induce, nil_append],
  simp only [walk.cons_append, induce, eq_self_iff_true, heq_iff_eq, true_and],
  apply p_ih, }

end walk

section add_delete_edges

lemma delete_edges_eq_iff (s : set (sym2 V)) :
  G.delete_edges s = G ↔ disjoint s G.edge_set :=
begin
  split,
  { rintro h ⟨u,v⟩ ⟨es,eG⟩,
    rw ←h at eG, obtain ⟨eG',es'⟩ := eG,
    exact es' es, },
  { rintro h, ext u v, split,
    exact λ x, x.left,
    rintro a, refine ⟨a,_⟩,
    rintro es, refine h ⟨es,a⟩, },
end

lemma delete_edge_eq_iff (u v) : G.delete_edges {⟦⟨u,v⟩⟧} = G ↔ ¬ G.adj u v :=
by { simp only [delete_edges_eq_iff, set.disjoint_singleton_left, mem_edge_set]}

def add_edges (G : simple_graph V) (s : set (sym2 V)) : simple_graph V :=
{ adj := λ a b, G.adj a b ∨ (a ≠ b) ∧ sym2.to_rel s a b,
  symm := λ a b, by
  { rintro (l|⟨ne,r⟩),
    { exact or.inl l.symm, } ,
    { apply or.inr, exact ⟨ne.symm,(sym2.to_rel_symmetric s r)⟩ } },
  loopless := λ a, by
  { rintro (l|⟨ne,r⟩), { exact G.loopless a l, }, { exact ne rfl }, } }

lemma le_add_edges  (G : simple_graph V) (s : set (sym2 V)) : G ≤ (G.add_edges s) := by
{ rintros a b h, exact or.inl h, }

lemma add_edges_le  (G T: simple_graph V) (s : set (sym2 V)) :
  G ≤ T → s ⊆ T.edge_set → G.add_edges s ≤ T :=
begin
  rintros GT sT,
  rintros u v (a|⟨ne,es⟩),
  { exact GT a, },
  { exact sT es, },
end

lemma le_delete_edges (G B : simple_graph V)  (s : set (sym2 V)) :
  B ≤ G → disjoint s B.edge_set → B ≤ G.delete_edges s := sorry

lemma add_edges_eq_iff (s : set (sym2 V)) :
  G.add_edges s = G ↔ (∀ u v, u ≠ v → ((⟦⟨u,v⟩⟧ : sym2 V) ∈ s) → G.adj u v) := sorry

lemma add_edge_eq_iff (u v) (h : u ≠ v) : G.add_edges {⟦⟨u,v⟩⟧} = G ↔ G.adj u v :=
begin
  simp [add_edges_eq_iff],
  split,
  { rintros h', exact h' u v h (by simp), },
  { rintro h' u v hn (⟨rfl,rfl⟩|⟨rfl,rfl⟩), exact h', exact h'.symm, },
end

lemma add_edge_adj (u v) (h : u ≠ v) : (G.add_edges {⟦⟨u,v⟩⟧}).adj u v := or.inr ⟨h,rfl⟩

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

lemma add_delete_edges {s : set (sym2 V)} (hs : disjoint s G.edge_set) :
  (G.add_edges s).delete_edges s = G := sorry

lemma add_delete_edge (u v) (h : ¬ G.adj u v) :
  (G.add_edges {⟦⟨u,v⟩⟧}).delete_edges {⟦⟨u,v⟩⟧} = G := sorry

lemma delete_add_edges {s : set (sym2 V)} (hs : s ⊆ G.edge_set) :
  (G.delete_edges s).add_edges s = G := sorry

lemma delete_add_edge (u v) (e : G.adj u v) :
  (G.delete_edges {⟦⟨u,v⟩⟧}).add_edges {⟦⟨u,v⟩⟧} = G := sorry

end add_delete_edges




namespace walk

variable (c : G.walk u u)

variables {V' : Type*} {G' : simple_graph V'} {f : G →g G'}

lemma is_cycle.to_delete_edges (s : set (sym2 V))
  {v : V} {p : G.walk v v} (h : p.is_cycle) (hp : ∀ (e : sym2 V), e ∈ p.edges → e ∉ s) :
  (p.to_delete_edges s hp).is_cycle := sorry

lemma map_is_cycle_of_injective (hinj : function.injective f) (hc : c.is_cycle) :
  (c.map f).is_cycle := sorry

protected lemma is_cycle.of_map {f : G →g G'} (hc : (c.map f).is_cycle) : c.is_cycle := sorry

lemma map_is_cycle_iff_of_injective (hinj : function.injective f) :
  (c.map f).is_cycle ↔ c.is_cycle := sorry

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
