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

This file is meant to contain results about the ends of
(usually locally finite and connected) graphs.
-/

set_option profiler true

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

/-
For a locally finite preconnected graph, the number of components outside of any finite set
is finite.
-/
lemma comp_out_finite [locally_finite G] (Gpc : preconnected G) (K : finset V) :
  finite (G.comp_out K) :=
begin
  classical,
  rcases K.eq_empty_or_nonempty with h|h,
  -- If K is empty, then removing K doesn't change the graph, which is connected, hence has a
  -- single connected component
  { cases h, dsimp [comp_out, out],
    rw set.compl_empty,
    haveI := @finite.of_subsingleton _ Gpc.subsingleton_connected_component,
    exact finite.of_equiv _ (connected_component.iso (induce_univ_iso G)).symm, },
  -- Otherwise, we consider the function `touch` mapping a connected component to one of its
  -- vertices adjacent to `K`.
  { let touch : G.comp_out K → {v : V | ∃ k : V, k ∈ K ∧ G.adj k v} :=
      λ C, let p := C.exists_adj_boundary_pair Gpc h in
        ⟨p.some.1, p.some.2, p.some_spec.2.1, p.some_spec.2.2.symm⟩,
    -- `touch` is injective
    have touch_inj : touch.injective := λ C D h', comp_out.eq_of_not_disjoint C D (by
    { rw set.not_disjoint_iff,
      use touch C,
      exact ⟨ (C.exists_adj_boundary_pair Gpc h).some_spec.1,
              h'.symm ▸ (D.exists_adj_boundary_pair Gpc h).some_spec.1⟩, }),
    -- `touch` has finite range
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

/--
In an infinite graph, the set of components out of a finite set is nonempty.
-/
lemma comp_out_nonempty_of_infinite [infinite V] (K : finset V) : nonempty (G.comp_out K) :=
begin
  obtain ⟨k,kK⟩ := set.infinite.nonempty (set.finite.infinite_compl $ K.finite_to_set),
  exact ⟨connected_component_mk _ ⟨k,kK⟩⟩,
end

/--
The `comp_out`s chosen by an end are all infinite.
-/
lemma end_comp_out_infinite (e : G.end) (K : (finset V)ᵒᵖ) : (e.val K).supp.infinite :=
begin
  apply (e.val K).inf_iff_in_all_ranges.mpr (λ L h, _),
  change opposite.unop K ⊆ opposite.unop (opposite.op L) at h,
  exact  ⟨e.val (opposite.op L), (e.prop (category_theory.op_hom_of_le h)).symm⟩,
end

/--
A locally finite preconnected infinite graph has at least one end.
-/
lemma nonempty_ends_of_infinite [Glf : locally_finite G] (Gpc : preconnected G) [Vi : infinite V] :
  G.end.nonempty :=
begin
  classical,
  exact @nonempty_sections_of_fintype_inverse_system _ _ _ G.comp_out_functor
    (λ K, @fintype.of_finite _ $ G.comp_out_finite Gpc K.unop)
    (λ K, G.comp_out_nonempty_of_infinite K.unop)
end

end simple_graph
