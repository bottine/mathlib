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
lemma end_comp_out_infinite
  (e : G.end)
  (K : (finset V)ᵒᵖ) : (e.val K).supp.infinite :=
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

noncomputable def end_to_local_end  [decidable_eq V] (K : (finset V)ᵒᵖ) (s : G.end) :
  (s.val K).subgraph.coe.end :=
begin
  fsplit,
  { rintro L,
    let L' := L.unop.image (subtype.val),
    refine @comp_out_mk _ _ ((s.val K).subgraph.coe)
             ⟨(s.val (opposite.op (L' ∪ K.unop))).nonempty.some, _⟩ _,
    { let vvLK := (s.val (opposite.op (L' ∪ K.unop))).nonempty,
      let v := vvLK.some,
      let hvLK := vvLK.some_spec,
      have vsK : v ∈ (s.val K).supp, by {
        refine set.mem_of_mem_of_subset hvLK _,
        refine (comp_out.hom_eq_iff_le _ _ _).mp (s.prop (category_theory.op_hom_of_le _)),
        refine finset.subset_union_right _ _, },
      exact vsK, },
    { let vvLK := (s.val (opposite.op (L' ∪ K.unop))).nonempty,
      let v := vvLK.some,
      let hvLK := vvLK.some_spec,
      have vsK : v ∈ (s.val K).supp, by
      { refine set.mem_of_mem_of_subset hvLK _,
        refine (comp_out.hom_eq_iff_le _ _ _).mp (s.prop (category_theory.op_hom_of_le _)),
        refine finset.subset_union_right _ _, },
      let := comp_out.not_mem_of_mem hvLK,
      simp_rw [opposite.unop_op, finset.mem_coe, finset.mem_union, not_or_distrib,
               finset.mem_image] at this,
      rw set.mem_compl_iff,
      exact λ h, this.left ⟨⟨v,vsK⟩, ⟨h,rfl⟩⟩,
     },
  },

  { rintro L L' LL',
    simp, apply comp_out.eq_of_not_disjoint,
    rw set.not_disjoint_iff, sorry, },
end

noncomputable def end_of_local_end [decidable_eq V] {K : (finset V)ᵒᵖ} {C : G.comp_out K.unop}
  (s : C.subgraph.coe.end) : G.end :=
begin
  fsplit,
  { rintro L,
    let L' := L.unop.preimage (subtype.val : C.subgraph.verts → V) (subtype.val_injective.inj_on _),
    let CL':= s.val (opposite.op L'),
    let vCL' := CL'.nonempty,
    refine @comp_out_mk _ _ G vCL'.some.val _,
     --let vvC := vCL'.some,
    let vh := vCL'.some_spec,
    let vnL := comp_out.not_mem_of_mem vh,
    convert vnL,
    simp only [set.mem_compl_iff, finset.mem_coe, opposite.unop_op, finset.mem_preimage,
               subtype.val_eq_coe], refl, },
  { rintro L L₂ hL, simp,
    apply comp_out.eq_of_not_disjoint,
    rw set.not_disjoint_iff,
    sorry

   }

end

lemma  end_of_local_end_agree [decidable_eq V] {K : (finset V)ᵒᵖ} {C : G.comp_out K.unop}
  (s : C.subgraph.coe.end) : (end_of_local_end G s).val K = C := sorry

/-
noncomputable def end_comp_out_equiv [decidable_eq V] (K : (finset V)ᵒᵖ) (C : G.comp_out K.unop) :
  {s : G.end // s.val K = C} ≃ C.subgraph.coe.end :=
begin
  classical,
  fsplit,
  { rintro ⟨⟨s,sec⟩,rfl⟩, fsplit,
    let C : G.comp_out K.unop := s K,
    have Cverts : (C : set V) = C.subgraph.verts := rfl,
    rintro L, dsimp only [comp_out_functor],

    let L' := L.unop.image (subtype.val),
    let vvLK := (s (opposite.op (L' ∪ K.unop))).nonempty,
    let v := vvLK.some,
    let hvLK := vvLK.some_spec,
    have vsK : v ∈ (s K).supp, by {
      apply set.mem_of_mem_of_subset hvLK _,
      apply (comp_out.hom_eq_iff_le _ _ _).mp (sec (category_theory.op_hom_of_le _)),
      apply finset.subset_union_right _ _, },
    refine comp_out_mk _ _,
    refine ⟨v,_⟩,
    change v ∈ (s K).supp,
    exact vsK,

    let := comp_out.not_mem_of_mem hvLK,
    simp_rw [opposite.unop_op, finset.mem_coe, finset.mem_union, not_or_distrib] at this,
    let thisl := this.left,
    rw finset.mem_image at thisl,
    simp only [set.mem_compl_iff, finset.mem_coe, subgraph.induce_verts, set_like.mem_coe, comp_out.mem_supp_iff, opposite.unop_op,
  finset.mem_union, finset.mem_image, subtype.val_eq_coe, exists_prop, subtype.exists, set_like.coe_mk,
  exists_and_distrib_right, exists_eq_right, not_exists, forall_exists_index] at thisl ⊢,
  rintro h,
  apply thisl,
  exact h,
    --simp at this,

    sorry, sorry, },
  sorry,
  sorry,
  sorry,
end
-/

end simple_graph
