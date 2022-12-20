/-
Copyright (c) 2022 Anand Rao, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao, Rémi Bottinelli
-/
import combinatorics.simple_graph.ends.defs
import data.finite.set
import data.finset.basic
/-!
# Properties of the ends of graphs

This file is meant to contain results about the ends of (locally finite connected) graphs.

-/

variables {V : Type} (G : simple_graph V)

namespace simple_graph

lemma ends_of_finite [finite V] : is_empty G.end :=
begin
  rw is_empty_iff,
  rintro ⟨s, -⟩,
  casesI nonempty_fintype V,
  obtain ⟨v, h⟩ := (s $ opposite.op finset.univ).nonempty,
  exact set.disjoint_iff.mp (s _).disjoint_right
    ⟨by simp only [opposite.unop_op, finset.coe_univ], h⟩,
end

/--!

## Ends of locally finite, connected graphs

-/

lemma comp_out_finite [locally_finite G] (Gpc : preconnected G) :
  ∀ (K : finset V), finite (G.comp_out K) :=
begin
  classical,
  rintro K,
  cases K.eq_empty_or_nonempty,
  -- If K is empty, then removing K doesn't change the graph, which is connected, hence has a
  -- single connected component
  { cases h, dsimp [comp_out, out],
    rw set.compl_empty,
    -- TODO: lemma : G.connected ↔ is_singleton G.connected_component
    haveI : finite G.connected_component, by
    { apply @finite.of_subsingleton _ _,
      constructor,
      apply connected_component.ind₂,
      simp only [connected_component.eq],
      exact Gpc, },
    apply finite.of_equiv (G.connected_component),
    exact (connected_component.iso (induce_univ_iso G)).symm, },
  -- Otherwise, we consider the function mapping a connected component to one of its vertices
  -- adjacent to `K`.
  -- This map is injective and its domain is finite.
  { let touch : G.comp_out K → {v : V | ∃ k : V, k ∈ K ∧ G.adj k v} :=
      λ C, let p := @comp_out.adj V G K Gpc h C in
        ⟨p.some.1, p.some.2, p.some_spec.2.1, p.some_spec.2.2.symm⟩,

    have touch_inj : touch.injective := λ C D h', comp_out.eq_of_not_disjoint C D (by
    { rw set.not_disjoint_iff,
      use touch C,
      exact ⟨ (comp_out.adj Gpc h C).some_spec.1,
              h'.symm ▸ (comp_out.adj Gpc h D).some_spec.1⟩, }),

    haveI : finite (set.range touch), by
    { apply @subtype.finite _ _ _,
      apply set.finite.to_subtype,
      have : {v : V | ∃ (k : V), k ∈ K ∧ G.adj k v} = finset.bUnion K (λ v, G.neighbor_finset v), by
      { ext v,
        simp only [set.mem_Union, exists_prop, set.mem_set_of_eq, finset.coe_bUnion,
                  finset.mem_coe, mem_neighbor_finset], },
      rw this,
      apply finset.finite_to_set, },

    apply finite.of_injective_finite_range touch_inj, },
end

lemma comp_out_nonempty_of_infinite [infinite V] :
  ∀ (K : finset V), nonempty (G.comp_out K) :=
begin
  rintro K,
  suffices : ((K : set V) ᶜ).nonempty,
  { obtain ⟨k,kK⟩ := this,
    exact ⟨connected_component_mk _ ⟨k,kK⟩⟩, },
  apply set.infinite.nonempty,
  apply set.finite.infinite_compl,
  apply finset.finite_to_set,
end

/--
A locally finite preconnected infinite graph has at least one end.
-/
lemma nonempty_ends_of_infinite [Glf : locally_finite G] (Gpc : preconnected G) [Vi : infinite V] :
  G.end.nonempty :=
@nonempty_sections_of_fintype_inverse_system' _ _ _ G.comp_out_functor
  (λ K, @fintype.of_finite _ $ simple_graph.comp_out_finite G Gpc K)
  (simple_graph.comp_out_nonempty_of_infinite G)

end simple_graph
