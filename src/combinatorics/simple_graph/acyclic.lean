/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import combinatorics.simple_graph.connectivity
import .aux
/-!

# Acyclic graphs and trees

This module introduces *acyclic graphs* (a.k.a. *forests*) and *trees*.

The structure of the proofs for `simple_graph.is_acyclic` and `simple_graph.is_tree`, including
supporting lemmas about `simple_graph.is_bridge`, generally follows the description for these
theorems for multigraphs from [Chou1994].

## Main definitions

* `simple_graph.is_acyclic` is a predicate for a graph having no cyclic walks
* `simple_graph.is_tree` is a predicate for a graph being a tree (a connected acyclic graph)

## Main statements

* `simple_graph.is_acyclic_iff` characterizes acyclicity in terms of uniqueness of paths between
  pairs of vertices.
* `simple_graph.is_acyclic_iff_forall_edge_is_bridge` characterizes acyclicity in terms of every
  edge being a bridge edge.
* `simple_graph.is_tree_iff` characterizes trees in terms of existence and uniqueness of paths
  between pairs of vertices from a nonempty vertex type.

## Tags

acyclic graphs, trees
-/

universes u v

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

/-- A graph is *acyclic* (or a *forest*) if it has no cycles. -/
def is_acyclic : Prop := ∀ (v : V) (c : G.walk v v), ¬c.is_cycle

/-- A *tree* is a connected acyclic graph. -/
def is_tree : Prop := G.connected ∧ G.is_acyclic

variables {G}

lemma is_acyclic_iff_forall_adj_is_bridge :
  G.is_acyclic ↔ ∀ {v w : V}, G.adj v w → G.is_bridge ⟦(v, w)⟧ :=
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
  G.is_acyclic ↔ ∀ (e ∈ G.edge_set), G.is_bridge e :=
by simp [is_acyclic_iff_forall_adj_is_bridge, sym2.forall]

lemma is_acyclic.path_unique {G : simple_graph V} (h : G.is_acyclic) {v w : V} (p q : G.path v w) :
  p = q :=
begin
  obtain ⟨p, hp⟩ := p,
  obtain ⟨q, hq⟩ := q,
  simp only,
  induction p with u pu pv pw ph p ih generalizing q,
  { cases q,
    { refl },
    { simpa [walk.is_path_def] using hq, } },
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

lemma is_acyclic_iff : G.is_acyclic ↔ ∀ (v w : V) (p q : G.path v w), p = q :=
⟨is_acyclic.path_unique, is_acyclic_of_path_unique⟩

lemma is_tree_iff : G.is_tree ↔ nonempty V ∧ ∀ (v w : V), ∃!(p : G.walk v w), p.is_path :=
begin
  classical,
  simp only [is_tree, is_acyclic_iff],
  split,
  { rintro ⟨hc, hu⟩,
    refine ⟨hc.nonempty, _⟩,
    intros v w,
    let q := (hc v w).some.to_path,
    use q,
    simp only [true_and, path.is_path],
    intros p hp,
    specialize hu v w ⟨p, hp⟩ q,
    simp only [←hu, subtype.coe_mk], },
  { rintro ⟨hV, h⟩,
    refine ⟨@connected.mk V _ _ hV, _⟩,
    { intros v w,
      obtain ⟨p, hp⟩ := h v w,
      use p, },
    { rintros v w ⟨p, hp⟩ ⟨q, hq⟩,
      simp only [unique_of_exists_unique (h v w) hp hq] } },
end

section min_max

variables (G) (T : simple_graph V) (hT : T.connected) (B : simple_graph V) (hB : B.is_acyclic)

lemma is_acyclic.le {G H : simple_graph V} (Ga : G.is_acyclic) : H ≤ G → H.is_acyclic :=
begin
  rintros h _ w wcycle,
  refine Ga _ _ (w.map_is_cycle_of_injective _ wcycle),
  exact simple_graph.hom.map_spanning_subgraphs h, exact function.injective_id,
end

lemma connected.le {G H : simple_graph V} (Hc : H.connected) : H ≤ G → G.connected :=
begin
  rintro h, rw connected_iff at Hc ⊢, refine ⟨_,Hc.2⟩,
  exact λ u v, ⟨(Hc.1 u v).some.map (simple_graph.hom.map_spanning_subgraphs h)⟩,
end

abbreviation is_max_acyclic := G ≤ T ∧ G.is_acyclic ∧ ∀ H, H ≤ T →  H.is_acyclic → H ≤ G

abbreviation is_min_connected := B ≤ G ∧ G.connected ∧ ∀ H, B ≤ H →  H.connected → G ≤ H

lemma is_max_acyclic_iff : G.is_max_acyclic T ↔
  G ≤ T ∧ G.is_acyclic ∧ ∀ e ∈ (T.edge_set \ G.edge_set), ¬ (G.add_edges {e}).is_acyclic := sorry

lemma is_min_connected_iff : G.is_min_connected B ↔
  B ≤ G ∧ G.connected ∧ ∀ e ∈ (G.edge_set \ B.edge_set), ¬ (G.delete_edges {e}).connected := sorry

lemma is_tree.is_max_acyclic [decidable_eq V] (hG : G.is_tree) {GT : G ≤ T} : G.is_max_acyclic T :=
begin
  rw is_max_acyclic_iff,
  use [GT,hG.right],
  rintro ⟨u,v⟩ ⟨eT,neG⟩,
  have : u ≠ v := ((mem_edge_set T).mp eT).ne,
  rintro Ge_ac,

  -- A path from `u` to `v` given by `connected`ness of `G`
  let p₁ : (G.add_edges {⟦⟨u,v⟩⟧}).path u v :=
    simple_graph.path.map
      (simple_graph.hom.map_spanning_subgraphs (le_add_edges G _))
      function.injective_id
      (hG.left.1 u v).some.to_path,

  -- The singleton path from `u` to `v` given by the edge `⟦⟨u,v⟩⟧`
  let p₂ : (G.add_edges {⟦⟨u,v⟩⟧}).path u v := path.singleton (add_edge_adj u v ‹u≠v›),

  -- Cannot be equal, since the edge is contained in one but not the other,
  have : p₁ ≠ p₂, by
  { rintro e,
    have : ⟦(u, v)⟧ ∉ p₁.val.edges := add_edge_hom_not_edges u v ‹u≠v› _,
    rw e at this,
    exact this (path.mk_mem_edges_singleton (add_edge_adj u v ‹u≠v›)), },

  -- By assumption, the extended graph is acyclic, hence unique paths, a contradiction
  exact this (Ge_ac.path_unique p₁ p₂),
end

lemma is_tree.is_min_connected [decidable_eq V] (hG : G.is_tree) {BG : B ≤ G} :
  G.is_min_connected B :=
begin
  rw is_min_connected_iff,
  use [BG,hG.left],
  rintro ⟨u,v⟩ ⟨eG,neB⟩,
  have : u ≠ v := ((mem_edge_set G).mp eG).ne,
  rintro Gne_co,

  let p₁ : G.path u v := simple_graph.path.map
      (simple_graph.hom.map_spanning_subgraphs (delete_edges_le G _))
      function.injective_id
      (Gne_co.1 u v).some.to_path,

  let p₂ : G.path u v := path.singleton ((mem_edge_set G).mp eG),

  have : p₁ ≠ p₂, by
  { rintro e,
    have : ⟦(u, v)⟧ ∉ p₁.val.edges := delete_edge_hom_not_edges u v eG _,
    rw e at this,
    exact this (path.mk_mem_edges_singleton ((mem_edge_set G).mp eG)), },

  exact this (hG.right.path_unique p₁ p₂),
end

lemma is_max_acyclic.is_connected [decidable_eq V] (hT : T.connected) :
  G.is_max_acyclic T → G.connected :=
begin
  rintros G_max_ac,
  rw is_max_acyclic_iff at G_max_ac,
  rw connected_iff, refine ⟨_,hT.2⟩,
  obtain ⟨GT,Gac,Gmax⟩ := G_max_ac,
  rintro u v,
  by_contra h,
  let w := (hT.1 u v).some,
  obtain ⟨x,y,e,hx',hy'⟩ := (hT.1 u v).some.split_along_set' ({x | G.reachable u x}) (by {simp,}) h,
  have hy : ¬ G.reachable x y, by {rintro h, apply hy', exact hx'.trans h, },
  have xney : x≠y, by { rintro h, rw h at hy, apply hy, reflexivity, },
  specialize Gmax ⟦⟨x,y⟩⟧
    ( by { rw [set.mem_diff, mem_edge_set], exact ⟨e, λ a, hy ⟨(path.singleton a).val⟩⟩ } ),
  dsimp [is_acyclic] at Gmax, push_neg at Gmax,
  obtain ⟨v,w,wc⟩ := Gmax,
  by_cases h : (⟦⟨x,y⟩⟧ : sym2 V) ∈ w.edges,
  { have : x ∈ w.support := simple_graph.walk.fst_mem_support_of_mem_edges w h,
    -- need to cover the two possible orders of appearence of x and y in the circuit
    -- Then, play with `take_until` and `drop_until` to build a path from x to y
    sorry,
   },
  { let w' : G.walk v v := sorry,
    have wc' : w'.is_cycle := sorry,
    exact Gac _ _ wc', },
  /-
  If this cycle contains e, then it does so at a unique position, so that it can be decomposed into p.cons e
  with p not containing e, and hence a path in G, contradicting unreachability.
  If this cycle does not contain e, we get a cycle in G, contradicting acyclicity
  -/

end

lemma is_min_connected.is_acyclic  (hB : B.is_acyclic)  : G.is_min_connected B → G.is_acyclic := sorry

end min_max

end simple_graph
