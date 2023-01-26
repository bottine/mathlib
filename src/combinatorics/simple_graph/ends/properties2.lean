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

protected def connected_component.lift_adj {β : Sort*} (f : V → β)
  (h : ∀ (v w : V), G.adj v w → f v = f w) : G.connected_component → β :=
quot.lift f (λ v w (h' : G.reachable v w), h'.elim $ λ vw, by
  { induction vw, refl, rw ←vw_ih ⟨vw_p⟩, exact h _ _ vw_h, } )

noncomputable def comp_out_to_option_local_comp_out [decidable_eq V] (K : finset V)
  (C : G.comp_out K) (L : finset $ subtype C.subgraph.verts) :
  ∀ (D : G.comp_out ((L.image subtype.val ∪ K) : finset V)), option (C.subgraph.coe.comp_out L) :=
begin
  fapply connected_component.lift_adj,
  { rintro vv,
    by_cases vC : vv.val ∈ C,
    { apply some,
      apply @comp_out_mk _ _ C.subgraph.coe ⟨vv.val, vC⟩ _,
      obtain ⟨v,h⟩ := vv,
      simp only [subgraph.induce_verts, subtype.exists, exists_and_distrib_right, exists_eq_right,
                 not_exists, finset.coe_image, set.compl_union, set.mem_inter_iff,
                 set.mem_compl_iff, set.mem_image, finset.mem_coe, finset.coe_union] at h,
      exact λ vL, h.1 vC vL, },
    { exact none, } },
  { rintro ⟨v,hv⟩ ⟨w,hw⟩,
    simp only [comap_adj, function.embedding.coe_subtype, subtype.coe_mk],
    rintro a, split_ifs with hvC hwC hwC,
    { rw [connected_component.eq],
      apply adj.reachable,
      simp only [set.mem_compl_iff, comap_adj, function.embedding.coe_subtype, subtype.coe_mk,
                 subgraph.coe_adj, subgraph.induce_adj, subgraph.top_adj_iff],
      exact ⟨hvC, hwC, a⟩, },
    { exact (hwC (comp_out.mem_of_adj v w hvC (λ wK, hw $ by { rw finset.coe_union, exact or.inr wK, }) a)).elim, },
    { exact (hvC (comp_out.mem_of_adj w v hwC (λ vK, hv $ by { rw finset.coe_union, exact or.inr vK, }) a.symm)).elim, },
    { refl, }, },
end

#print comp_out_to_option_local_comp_out

lemma comp_out_to_option_local_comp_out_hom [decidable_eq V] (K : finset V) (C : G.comp_out K)
  (L L' : finset $ subtype C.subgraph.verts) (LL' : L' ⊆ L)
  (KLL' : (L'.image subtype.val) ∪ K ⊆ (L.image subtype.val) ∪ K) -- this follows from `LL'`
  (D : G.comp_out ((L.image subtype.val) ∪ K : finset V)) :
  (G.comp_out_to_option_local_comp_out K C L D).map (comp_out.hom LL') =
   G.comp_out_to_option_local_comp_out K C L' (D.hom $ KLL') :=
begin
  classical,
  dsimp only [comp_out_to_option_local_comp_out, connected_component.lift_adj, comp_out.hom,
              connected_component.map, connected_component.lift, connected_component_mk],
  revert D,
  refine quot.ind _,
  rintro ⟨v,hv⟩,
  by_cases vC : v ∈ C,
  { simp only [set.mem_compl_iff, subtype.val_eq_coe, option.map_some', dif_pos vC,
               rel_hom.coe_fn_mk, subtype.coe_mk],
    dsimp only [comp_out.hom, connected_component.map, comp_out_mk, connected_component_mk,
                connected_component.lift, out_hom],
    simp only [subtype.coe_mk, rel_hom.coe_fn_mk, set.mem_compl_iff],
    congr, },
  { simp only [rel_hom.coe_fn_mk, subtype.coe_mk, dif_neg vC, option.map_none'], },
end

lemma comp_out_to_option_local_comp_out_some [decidable_eq V] (K : finset V) (C : G.comp_out K)
  (L : finset $ subtype C.subgraph.verts) :
  ∀ (D : G.comp_out ((L.image subtype.val) ∪ K : finset _)) (DC : D.supp ⊆ C),
  ∃ (E : C.subgraph.coe.comp_out L), G.comp_out_to_option_local_comp_out K C L D = some E :=
begin
  classical,
  dsimp only [comp_out_to_option_local_comp_out, connected_component.lift_adj],
  refine quot.ind _,
  rintro ⟨v,hv⟩ DC,
  have : v ∈ C, by
  { apply set.mem_of_mem_of_subset _ DC,
    apply comp_out_mk_mem, },
  simp only [set.mem_compl_iff, dif_pos this],
  refine ⟨_, rfl⟩,
end

noncomputable def comp_out_to_local_comp_out  [decidable_eq V] (K : finset V) (C : G.comp_out K)
  (L : finset $ subtype C.subgraph.verts) (D : G.comp_out ((L.image subtype.val) ∪ K : finset _))
  (DC : D.supp ⊆ C) : C.subgraph.coe.comp_out L :=
(G.comp_out_to_option_local_comp_out_some K C L D DC).some

lemma comp_out_to_local_comp_out_hom [decidable_eq V] (K : finset V) (C : G.comp_out K)
  (L L' : finset $ subtype C.subgraph.verts) (LL' : L' ⊆ L)
  (D : G.comp_out ((L.image subtype.val) ∪ K : finset _))
  (CD : D.supp ⊆ C)  -- this follows from `CD'`
  (KLL' : (L'.image subtype.val) ∪ K ⊆ (L.image subtype.val) ∪ K) -- this follows from `LL'`
  (CD' : (D.hom KLL').supp ⊆ C) :
  (G.comp_out_to_local_comp_out K C L D CD).hom LL' =
   G.comp_out_to_local_comp_out K C L' (D.hom KLL') CD' :=
begin
  dsimp only [comp_out_to_option_local_comp_out_some, comp_out_to_local_comp_out],
  let := G.comp_out_to_option_local_comp_out_hom K C L L' LL' KLL' D,
  rw [(G.comp_out_to_option_local_comp_out_some K C L D CD).some_spec,
      (G.comp_out_to_option_local_comp_out_some K C L' (D.hom $ KLL') CD').some_spec,
      option.map_some'] at this,
  simpa using this,
end

def local_comp_out_to_comp_out [decidable_eq V] (K : finset V) (C : G.comp_out K) (L : finset V) :
  C.subgraph.coe.comp_out
    (L.preimage subtype.val (subtype.val_injective.inj_on _) : finset ↥(C.subgraph.verts)) → G.comp_out L :=
begin
  fapply connected_component.lift_adj,
  { rintro vv,
    fapply comp_out_mk,
    { exact vv.val.val, },
    { simpa using vv.prop, }, },
  { rintro ⟨⟨v,vC⟩,hv⟩ ⟨⟨w,wC⟩,hw⟩ a,
    simp only [connected_component.eq],
    simp only [set.mem_compl_iff, comap_adj, function.embedding.coe_subtype, subtype.coe_mk,
                subgraph.coe_adj, subgraph.induce_adj, set_like.mem_coe, comp_out.mem_supp_iff,
                subgraph.top_adj_iff] at a,
    apply adj.reachable,
    simp only [comap_adj, function.embedding.coe_subtype, subtype.coe_mk],
    exact a.2.2, },
end

lemma local_comp_out_to_comp_out_hom [decidable_eq V] (K : finset V) (C : G.comp_out K)
  (L L' : finset V) (h : L' ⊆ L)
  (D : C.subgraph.coe.comp_out (L.preimage subtype.val (subtype.val_injective.inj_on _) : finset ↥(C.subgraph.verts))) :
  (local_comp_out_to_comp_out G K C L D).hom h =
  local_comp_out_to_comp_out G K C L' (D.hom $ by {simp, apply set.preimage_mono, norm_cast, exact h}) :=
begin
  revert D,
  refine quot.ind _,
  rintro ⟨⟨v,vC⟩,hv⟩,
  refl,
end

noncomputable def end_comp_out_equiv [decidable_eq V] (K : (finset V)ᵒᵖ) (C : G.comp_out K.unop) :
  {s : G.end // s.val K = C} ≃ C.subgraph.coe.end :=
{ to_fun := λ ⟨⟨s,sec⟩,h⟩, by
  { fsplit,
    { rintro L,
      fapply comp_out_to_local_comp_out,
      { exact s (opposite.op $ (finset.image subtype.val L.unop) ∪ (K.unop)), },
      { simp_rw ←h,
        have := @sec (opposite.op ((finset.image subtype.val L.unop) ∪ K.unop : finset _)) K _,
        swap,
        { have : K = opposite.op K.unop, by simp only [opposite.op_unop],
          nth_rewrite_rhs 0 this,
          apply category_theory.op_hom_of_le,
          apply finset.subset_union_right, },
        rw ←this,
        apply comp_out.subset_hom, }, },
    { sorry, }, },
  inv_fun := λ s, sorry,
  left_inv := λ s, sorry,
  right_inv := λ s, sorry
 }

end simple_graph
