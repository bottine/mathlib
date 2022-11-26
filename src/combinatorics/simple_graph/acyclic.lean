/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.from_edge_set
/-!

# Acyclic graphs and trees

This module introduces *acyclic graphs* (a.k.a. *forests*) and *trees*.

## Main definitions

* `simple_graph.is_acyclic` is a predicate for a graph having no cyclic walks
* `simple_graph.is_tree` is a predicate for a graph being a tree (a connected acyclic graph)

## Main statements

* `simple_graph.is_acyclic_iff_path_unique` characterizes acyclicity in terms of uniqueness of
  paths between pairs of vertices.
* `simple_graph.is_acyclic_iff_forall_edge_is_bridge` characterizes acyclicity in terms of every
  edge being a bridge edge.
* `simple_graph.is_tree_iff_exists_unique_path` characterizes trees in terms of existence and
  uniqueness of paths between pairs of vertices from a nonempty vertex type.

## References

The structure of the proofs for `simple_graph.is_acyclic` and `simple_graph.is_tree`, including
supporting lemmas about `simple_graph.is_bridge`, generally follows the high-level description
for these theorems for multigraphs from [Chou1994].

## Tags

acyclic graphs, trees
-/

universes u v

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

/-- A graph is *acyclic* (or a *forest*) if it has no cycles. -/
def is_acyclic : Prop := ∀ (v : V) (c : G.walk v v), ¬c.is_cycle

/-- A *tree* is a connected acyclic graph. -/
@[mk_iff, protect_proj] structure is_tree : Prop :=
(is_connected : G.connected)
(is_acyclic : G.is_acyclic)

variables {G}

lemma is_acyclic_iff_forall_adj_is_bridge :
  G.is_acyclic ↔ ∀ ⦃v w : V⦄, G.adj v w → G.is_bridge ⟦(v, w)⟧ :=
begin
  simp_rw [is_bridge_iff_adj_and_forall_cycle_not_mem],
  split,
  { intros ha v w hvw,
    apply and.intro hvw,
    intros u p hp,
    exact absurd hp (ha _ p), },
  { rintros hb v (_ | @⟨_, _, _, ha, p⟩) hp,
    { exact hp.not_of_nil },
    { specialize hb ha,
      apply hb.2 _ hp,
      rw [walk.edges_cons],
      apply list.mem_cons_self } },
end

lemma is_acyclic_iff_forall_edge_is_bridge :
  G.is_acyclic ↔ ∀ ⦃e⦄, e ∈ G.edge_set → G.is_bridge e :=
by simp [is_acyclic_iff_forall_adj_is_bridge, sym2.forall]

lemma is_acyclic.path_unique {G : simple_graph V} (h : G.is_acyclic) {v w : V} (p q : G.path v w) :
  p = q :=
begin
  obtain ⟨p, hp⟩ := p,
  obtain ⟨q, hq⟩ := q,
  simp only,
  induction p with u pu pv pw ph p ih generalizing q,
  { rw walk.is_path_iff_eq_nil at hq,
    exact hq.symm, },
  { rw is_acyclic_iff_forall_adj_is_bridge at h,
    specialize h ph,
    rw is_bridge_iff_adj_and_forall_walk_mem_edges at h,
    replace h := h.2 (q.append p.reverse),
    simp only [walk.edges_append, walk.edges_reverse, list.mem_append, list.mem_reverse] at h,
    cases h,
    { cases q,
      { simpa [walk.is_path_def] using hp },
      { rw walk.cons_is_path_iff at hp hq,
        simp only [walk.edges_cons, list.mem_cons_iff, sym2.eq_iff] at h,
        obtain (⟨h,rfl⟩ | ⟨rfl,rfl⟩) | h := h,
        { rw [ih hp.1 _ hq.1] },
        { simpa using hq },
        { exact absurd (walk.fst_mem_support_of_mem_edges _ h) hq.2 } } },
    { rw walk.cons_is_path_iff at hp,
      exact absurd (walk.fst_mem_support_of_mem_edges _ h) hp.2 } }
end

lemma is_acyclic_of_path_unique (h : ∀ (v w : V) (p q : G.path v w), p = q) : G.is_acyclic :=
begin
  intros v c hc,
  simp only [walk.is_cycle_def, ne.def] at hc,
  cases c,
  { exact absurd rfl hc.2.1 },
  { simp only [walk.cons_is_trail_iff, not_false_iff, walk.support_cons,
      list.tail_cons, true_and] at hc,
    specialize h _ _ ⟨c_p, by simp only [walk.is_path_def, hc.2]⟩ (path.singleton (G.symm c_h)),
    simp only [path.singleton] at h,
    simpa [-quotient.eq, sym2.eq_swap, h] using hc },
end

lemma is_acyclic_iff_path_unique : G.is_acyclic ↔ ∀ ⦃v w : V⦄ (p q : G.path v w), p = q :=
⟨is_acyclic.path_unique, is_acyclic_of_path_unique⟩

lemma is_tree_iff_exists_unique_path :
  G.is_tree ↔ nonempty V ∧ ∀ (v w : V), ∃! (p : G.walk v w), p.is_path :=
begin
  classical,
  rw [is_tree_iff, is_acyclic_iff_path_unique],
  split,
  { rintro ⟨hc, hu⟩,
    refine ⟨hc.nonempty, _⟩,
    intros v w,
    let q := (hc v w).some.to_path,
    use q,
    simp only [true_and, path.is_path],
    intros p hp,
    specialize hu ⟨p, hp⟩ q,
    exact subtype.ext_iff.mp hu, },
  { unfreezingI { rintro ⟨hV, h⟩ },
    refine ⟨connected.mk _, _⟩,
    { intros v w,
      obtain ⟨p, hp⟩ := h v w,
      exact p.reachable, },
    { rintros v w ⟨p, hp⟩ ⟨q, hq⟩,
      simp only [unique_of_exists_unique (h v w) hp hq] } },
end

section min_max

variables (G) (T : simple_graph V) (hT : T.connected) (B : simple_graph V) (hB : B.is_acyclic)

lemma is_acyclic.le {G H : simple_graph V} (Gac : G.is_acyclic) : H ≤ G → H.is_acyclic :=
λ h _ w wcycle, Gac _
  (w.map (simple_graph.hom.map_spanning_subgraphs h))
  (walk.map_is_cycle_of_injective (function.injective_id) wcycle)

lemma connected.le {G H : simple_graph V} (Hc : H.connected) : H ≤ G → G.connected :=
begin
  rintro h, rw connected_iff at Hc ⊢, refine ⟨_,Hc.2⟩,
  exact λ u v, ⟨(Hc.1 u v).some.map (simple_graph.hom.map_spanning_subgraphs h)⟩,
end

abbreviation is_max_acyclic := G ≤ T ∧ G.is_acyclic ∧ ∀ H, G ≤ H → H ≤ T → H.is_acyclic → H = G

abbreviation is_min_connected := B ≤ G ∧ G.connected ∧ ∀ H, B ≤ H → H ≤ G → H.connected → H = G

lemma is_max_acyclic_iff : G.is_max_acyclic T ↔
  G ≤ T ∧
  G.is_acyclic ∧
  ∀ e ∈ (T.edge_set \ G.edge_set), ¬ (G ⊔ from_edge_set {e}).is_acyclic :=
begin
  split,
  { rintro ⟨GT,Gac,Gmax⟩, refine ⟨GT, Gac, _⟩,
    rintro ⟨u,v⟩ ⟨eT,neG⟩ Geac,
    apply neG, clear neG,
    suffices : G ⊔ from_edge_set {⟦(u, v)⟧} = G, by
    { simp only [sup_eq_left] at this,
      apply this,
      simpa only [from_edge_set_adj, set.mem_singleton, true_and] using adj.ne eT, },
    apply Gmax _ _ _ Geac,
    { simp only [le_sup_left], },
    { rw ←set.singleton_subset_iff at eT,
      simp only [GT, sup_le_iff, true_and, from_edge_set_le, eT], }, },
  { rintro ⟨GT,Gac,Gmax⟩, refine ⟨GT, Gac, _⟩,
    rintro H GH HT Hac,
    by_contra h,
    have h' : ¬ H ≤ G := λ HG, h (le_antisymm HG GH),
    simp only [has_le.le, simple_graph.is_subgraph] at h',
    push_neg at h',
    obtain ⟨u, v, ⟨Ha,nGa⟩⟩ := h',
    apply Gmax
      (⟦⟨u,v⟩⟧ : sym2 V)
      (by {simp only [set.mem_diff, mem_edge_set], exact ⟨HT Ha, nGa⟩}),
    apply Hac.le,
    rw [←mem_edge_set,←set.singleton_subset_iff] at Ha,
    simp only [GH, Ha, from_edge_set_le, sup_le_iff, and_self], },
end

lemma is_min_connected_iff : G.is_min_connected B ↔
  B ≤ G ∧
  G.connected ∧
  ∀ e ∈ (G.edge_set \ B.edge_set), ¬ (G \ from_edge_set{e}).connected :=
begin
  split,
  { rintro ⟨BG,Gco,Gmin⟩, refine ⟨BG, Gco, _⟩,
    rintro ⟨u,v⟩ ⟨eG,neB⟩ Gneco,
    change ¬ B.adj u v at neB,
    change (⟦⟨u,v⟩⟧ : sym2 V) ∈ G.edge_set at eG,
    suffices h : G \ from_edge_set {⟦(u, v)⟧} = G, by
    { rw ←h at eG, simpa using eG, }, -- Any kind of  `simpx [←h]` doesn't work?
    apply Gmin _ _ _ Gneco,
    { simp [BG, disjoint_iff],
      apply edge_set_injective,
      simp [set.eq_empty_iff_forall_not_mem],
      rintro e eB rfl,
      exact (neB eB).elim, },
    { simp only [sdiff_le_iff, le_sup_right], }, },
  { rintro ⟨BG,Gco,Gmin⟩, refine ⟨BG, Gco, _⟩,
    rintro H BH HG Hco,
    by_contra h,
    have h' : ¬ G ≤ H := λ GH, h (le_antisymm HG GH),
    simp only [has_le.le, simple_graph.is_subgraph] at h',
    push_neg at h',
    obtain ⟨u, v, ⟨Ga,nHa⟩⟩ := h',
    apply Gmin
      (⟦⟨u,v⟩⟧ : sym2 V)
      (by {simp only [set.mem_diff, mem_edge_set], exact ⟨Ga, λ h, nHa (BH h)⟩}),
    refine Hco.le _,
    simp [HG, disjoint_iff],
    apply edge_set_injective,
    simp [set.eq_empty_iff_forall_not_mem],
    rintro a aH rfl,
    exact (nHa aH).elim, },
end

lemma is_tree.is_max_acyclic [decidable_eq V] (hG : G.is_tree) {GT : G ≤ T} : G.is_max_acyclic T :=
begin
  rw is_max_acyclic_iff,
  use [GT,hG.is_acyclic],
  rintro ⟨u,v⟩ ⟨eT,neG⟩,
  have : u ≠ v := ((mem_edge_set T).mp eT).ne,
  rintro Ge_ac,

  -- A path from `u` to `v` given by `connected`ness of `G`
  let p₁ : (G ⊔ from_edge_set {⟦⟨u,v⟩⟧}).path u v :=
    simple_graph.path.map
      (simple_graph.hom.map_spanning_subgraphs (by simp))
      function.injective_id
      (hG.is_connected.1 u v).some.to_path,

  -- The singleton path from `u` to `v` given by the edge `⟦⟨u,v⟩⟧`
  let p₂ : (G ⊔ from_edge_set {⟦⟨u,v⟩⟧}).path u v := path.singleton (by simp [this]),

  -- Cannot be equal, since the edge is contained in one but not the other,
  have : p₁ ≠ p₂, by
  { rintro e,
    have : ⟦(u, v)⟧ ∉ p₁.val.edges := λ h, by
    { simp only [subtype.val_eq_coe, path.map_coe, walk.edges_map, list.mem_map,
      hom.map_spanning_subgraphs_apply, sym2.map_id', id.def, exists_eq_right] at h,
      apply neG (walk.edges_subset_edge_set _ h), },
    rw e at this,
    apply this,
    simp only [subtype.val_eq_coe, path.singleton_coe, walk.edges_cons, walk.edges_nil,
               list.mem_singleton], },

  -- By assumption, the extended graph is acyclic, hence unique paths, a contradiction
  exact this (Ge_ac.path_unique p₁ p₂),
end

lemma is_tree.is_min_connected [decidable_eq V] (hG : G.is_tree) {BG : B ≤ G} :
  G.is_min_connected B :=
begin
  rw is_min_connected_iff,
  use [BG,hG.is_connected],
  rintro ⟨u,v⟩ ⟨eG,neB⟩ Gne_co,

  let p₁ : G.path u v := simple_graph.path.map
      (simple_graph.hom.map_spanning_subgraphs (by simp))
      function.injective_id
      (Gne_co.1 u v).some.to_path,

  let p₂ : G.path u v := path.singleton ((mem_edge_set G).mp eG),

  have : p₁ ≠ p₂, by
  { rintro e,
    have : ⟦(u, v)⟧ ∉ p₁.val.edges := λ h, by
    { simp only [subtype.val_eq_coe, path.map_coe, walk.edges_map, list.mem_map,
                 hom.map_spanning_subgraphs_apply, sym2.map_id', id.def, exists_eq_right] at h,
      replace h := walk.edges_subset_edge_set _ h,
      simp only [from_edge_set_sdiff, from_edge_set_edge_set, mem_edge_set, sdiff_adj,
                 from_edge_set_adj, set.mem_singleton_iff, not_and, not_not] at h
                {contextual := tt},
      apply h.left.ne (h.right rfl), },
    rw e at this,
    exact this (path.mk_mem_edges_singleton ((mem_edge_set G).mp eG)), },

  exact this (hG.is_acyclic.path_unique p₁ p₂),
end

lemma is_max_acyclic.is_connected [decidable_eq V] (hT : T.connected) :
  G.is_max_acyclic T → G.connected :=
begin
  rintros G_max_ac,
  rw is_max_acyclic_iff at G_max_ac, obtain ⟨GT,Gac,Gmax⟩ := G_max_ac,
  rw connected_iff, refine ⟨_,hT.2⟩,
  rintro u v,
  by_contra h,
  obtain ⟨x,y,e,hx',hy'⟩ := (hT.1 u v).some.disagreeing_adj_pair ({x | G.reachable u x}) (by {simp,}) h,
  have hy : ¬ G.reachable x y := λ h, hy' (hx'.trans h),
  have xnay : ¬ G.adj x y := λ a, hy ⟨(path.singleton a).val⟩,
  have xney : x ≠ y := e.ne,
  have hG : G = (G ⊔ from_edge_set {⟦⟨x,y⟩⟧}) \ from_edge_set {⟦⟨x,y⟩⟧}, by
  { simp only [sup_sdiff_right_self],
    refine le_antisymm _ (sdiff_le),
    simp only [order.boolean_algebra.le_sdiff, le_refl, true_and],
    rw [disjoint.comm, from_edge_set_disjoint_iff],
    simp only [xnay, set.disjoint_singleton_left, mem_edge_set, not_false_iff], },
  specialize Gmax ⟦⟨x,y⟩⟧
    ( by { rw [set.mem_diff, mem_edge_set], exact ⟨e, xnay⟩ } ),
  dsimp only [is_acyclic] at Gmax,
  push_neg at Gmax,
  obtain ⟨v,w,wc⟩ := Gmax,
  by_cases h : (⟦⟨x,y⟩⟧ : sym2 V) ∈ w.edges,
  { apply hy, rw hG,
    exact (adj_and_reachable_delete_edges_iff_exists_cycle.mpr ⟨v,w,wc,h⟩).right, },
  { rw hG at Gac,
    refine Gac v (w.transfer _ (λ e ew, _)) (wc.transfer _),
    simp only [edge_set_sdiff, edge_set_from_edge_set, edge_set_sdiff_sdiff_is_diag, set.mem_diff,
               set.mem_singleton_iff],
    split,
    { exact (w.edges_subset_edge_set ew), },
    { rintro rfl, exact h ew, }, },
end


lemma is_min_connected.is_acyclic (hB : B.is_acyclic) : G.is_min_connected B → G.is_acyclic :=
begin
  rintro G_min_co,
  rw is_min_connected_iff at G_min_co,
  obtain ⟨BG,Gco,Gmin⟩ := G_min_co,
  rintro c w wc,
  have : ∃ e, e ∈ w.edges ∧ e ∉ B.edge_set, by
  { by_contra h, push_neg at h,
    exact hB c (w.transfer B h) (walk.is_cycle.transfer wc h), },
  obtain ⟨⟨u,v⟩,⟨ew,neB⟩⟩ := this,
  apply Gmin ⟦⟨u,v⟩⟧ ⟨walk.edges_subset_edge_set w ew, neB⟩,
  rw connected_iff at Gco ⊢, refine ⟨_,Gco.right⟩,
  clear neB Gmin BG hB B,
  obtain ⟨_,⟨p'⟩⟩ := (adj_and_reachable_delete_edges_iff_exists_cycle.mpr ⟨c,w,wc,ew⟩),
  let p : G.walk u v := p'.map (hom.map_spanning_subgraphs (by simp)),
  have hp : (⟦⟨u,v⟩⟧ : sym2 V) ∉ p.edges := λ h, by
  { simp only [walk.edges_map, list.mem_map, hom.map_spanning_subgraphs_apply, sym2.map_id',
               id.def, exists_eq_right] at h,
    simpa using p'.edges_subset_edge_set h, },
  rintros x y,
  obtain ⟨wG⟩ := Gco.left x y,
  let wG' := wG.substitute p hp,
  let hwG' := wG.substitute_edge_not_mem p hp,
  constructor,
  apply wG'.transfer _ _,
  rintro e ewG', simp,
  refine ⟨wG'.edges_subset_edge_set ewG',λ h, _⟩,
  rw ←h at hwG',
  apply hwG' ewG',
end

end min_max

end simple_graph
