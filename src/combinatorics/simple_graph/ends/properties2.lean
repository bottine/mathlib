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

open opposite category_theory

protected def connected_component.lift_adj {β : Sort*} (f : V → β)
  (h : ∀ (v w : V), G.adj v w → f v = f w) : G.connected_component → β :=
quot.lift f (λ v w (h' : G.reachable v w), h'.elim $ λ vw, by
  { induction vw, refl, rw ←vw_ih ⟨vw_p⟩, exact h _ _ vw_h, } )

/- -- Less tactic'y
def comp_out_to_option_local_comp_out [decidable_eq V] (K : finset V)
  (C : G.comp_out K) (L : finset $ subtype C.supp) [decidable_pred C.supp] :
  ∀ (D : G.comp_out ((L.image subtype.val ∪ K) : finset V)), option (C.coe.comp_out L) :=
connected_component.lift_adj _
  (λ vv,
    if vC : vv.val ∈ C.supp then
      some $ @comp_out_mk _ _ C.coe ⟨vv.val, vC⟩ $
      by
      { obtain ⟨v,h⟩ := vv,
        simp only [subgraph.induce_verts, subtype.exists, exists_and_distrib_right, exists_eq_right,
                   not_exists, finset.coe_image, set.compl_union, set.mem_inter_iff,
                   set.mem_compl_iff, set.mem_image, finset.mem_coe, finset.coe_union] at h,
        exact λ vL, h.1 vC vL, }
    else
      none )
  (λ ⟨v,hv⟩ ⟨w,hw⟩ a, by
    { simp only [comap_adj, function.embedding.coe_subtype, subtype.coe_mk],
      split_ifs with hvC hwC hwC,
      { rw [connected_component.eq],
        apply adj.reachable,
        simpa only [comap_adj, function.embedding.coe_subtype, subtype.coe_mk] using a, },
      { exact (hwC (comp_out.mem_of_adj v w hvC (λ wK, hw $ by { rw finset.coe_union, exact or.inr wK, }) a)).elim, },
      { exact (hvC (comp_out.mem_of_adj w v hwC (λ vK, hv $ by { rw finset.coe_union, exact or.inr vK, }) a.symm)).elim, },
      { refl, }, })
-/

noncomputable def comp_out_to_option_local_comp_out [decidable_eq V] (K : finset V)
  (C : G.comp_out K) (L : finset $ subtype C.supp) :
  ∀ (D : G.comp_out ((L.image subtype.val ∪ K) : finset V)), option (C.coe.comp_out L) :=
begin
  fapply connected_component.lift_adj,
  { rintro vv,
    by_cases vC : vv.val ∈ C,
    { refine some (@comp_out_mk _ _ C.coe ⟨vv.val, vC⟩ _),
      obtain ⟨v,h⟩ := vv,
      rintro vL, apply h,
      simp only [set.mem_compl_iff, finset.mem_coe, finset.coe_union, finset.coe_image,
                 set.mem_union, set.mem_image, subtype.exists, exists_and_distrib_right,
                 exists_eq_right],
      rw [comp_out.mem_supp_iff] at vC,
      exact or.inl ⟨vC, vL⟩, },
    { exact none, } },
  { rintro ⟨v,hv⟩ ⟨w,hw⟩,
    rintro a,
    split_ifs with hvC hwC hwC,
    { rw [connected_component.eq],
      apply adj.reachable,
      simpa only [comap_adj, function.embedding.coe_subtype, subtype.coe_mk] using a, },
    { exact (hwC (comp_out.mem_of_adj v w hvC (λ wK, hw $ by { rw finset.coe_union, exact or.inr wK, }) a)).elim, },
    { exact (hvC (comp_out.mem_of_adj w v hwC (λ vK, hv $ by { rw finset.coe_union, exact or.inr vK, }) a.symm)).elim, },
    { refl, }, },
end

lemma comp_out_to_option_local_comp_out_hom [decidable_eq V] (K : finset V) (C : G.comp_out K)
  (L L' : finset $ subtype C.supp) (LL' : L' ⊆ L)
  (KLL' : (L'.image subtype.val) ∪ K ⊆ (L.image subtype.val) ∪ K) -- this follows from `LL'`
  (D : G.comp_out ((L.image subtype.val) ∪ K : finset V)) :
  (G.comp_out_to_option_local_comp_out K C L D).map (comp_out.hom LL') =
   G.comp_out_to_option_local_comp_out K C L' (D.hom $ KLL') :=
begin
  classical,
  dsimp only [comp_out_to_option_local_comp_out, connected_component.lift_adj, comp_out.hom,
              connected_component.map, connected_component.lift, connected_component_mk],
  refine quot.induction_on D _,
  rintro ⟨v,hv⟩,
  by_cases vC : v ∈ C,
  { simp only [option.map_some', dif_pos vC, comp_out.hom, connected_component.map, comp_out_mk,
               connected_component_mk, connected_component.lift, out_hom, subtype.coe_mk,
               rel_hom.coe_fn_mk],
    congr, },
  { simp only [rel_hom.coe_fn_mk, subtype.coe_mk, dif_neg vC, option.map_none'], },
end

lemma comp_out_to_option_local_comp_out_some [decidable_eq V] (K : finset V) (C : G.comp_out K)
  (L : finset $ subtype C.supp) :
  ∀ (D : G.comp_out ((L.image subtype.val) ∪ K : finset _)) (DC : D.supp ⊆ C),
  ∃ (E : C.coe.comp_out L), G.comp_out_to_option_local_comp_out K C L D = some E :=
begin
  classical,
  refine quot.ind _,
  rintro ⟨v,hv⟩ DC,
  have : v ∈ C := DC (comp_out_mk_mem G hv),
  simp only [comp_out_to_option_local_comp_out, connected_component.lift_adj, dif_pos this],
  refine ⟨_, rfl⟩,
end

noncomputable def comp_out_to_local_comp_out  [decidable_eq V] (K : finset V) (C : G.comp_out K)
  (L : finset $ subtype C.supp) (D : G.comp_out ((L.image subtype.val) ∪ K : finset _))
  (DC : D.supp ⊆ C) : C.coe.comp_out L :=
(G.comp_out_to_option_local_comp_out_some K C L D DC).some

lemma comp_out_to_local_comp_out_hom [decidable_eq V] (K : finset V) (C : G.comp_out K)
  (L L' : finset $ subtype C.supp) (LL' : L' ⊆ L)
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
  simpa only using this,
end

def local_comp_out_to_comp_out [decidable_eq V] (K : finset V) (C : G.comp_out K) (L : finset V) :
  C.coe.comp_out
    (L.preimage subtype.val (subtype.val_injective.inj_on _) : finset ↥(C.supp)) → G.comp_out L :=
connected_component.lift_adj _
  (λ vv, @comp_out_mk _ _ _ vv.val.val
          (by { simpa only [finset.coe_preimage] using subtype.prop vv, }))
  (λ ⟨⟨v,vC⟩,hv⟩ ⟨⟨w,wC⟩,hw⟩ a, by
    { simp only [connected_component.eq],
      apply adj.reachable,
      simpa only [comap_adj, function.embedding.coe_subtype, subtype.coe_mk] using a, })

lemma local_comp_out_to_comp_out_hom [decidable_eq V] (K : finset V) (C : G.comp_out K)
  (L L' : finset V) (h : L' ⊆ L)
  (D : C.coe.comp_out (L.preimage subtype.val (subtype.val_injective.inj_on _) : finset ↥(C.supp))) :
  (local_comp_out_to_comp_out G K C L D).hom h =
  local_comp_out_to_comp_out G K C L' (D.hom $ finset.monotone_preimage subtype.val_injective h ) :=
quot.induction_on D (λ _, rfl)

noncomputable def end_comp_out_equiv [decidable_eq V] (K : (finset V)ᵒᵖ) (C : G.comp_out K.unop) :
  {s : G.end // s.val K = C} ≃ C.coe.end :=
{ to_fun := λ ⟨⟨s,sec⟩,h⟩, by
  begin
    fsplit,
    { rintro L,
      fapply comp_out_to_local_comp_out G K.unop C _ (s (op $ (L.unop.image subtype.val) ∪ (K.unop))),
      { simp_rw [←h, ←@sec (op ((L.unop.image subtype.val) ∪ K.unop : finset _)) K
                     (op_hom_of_le (finset.subset_union_right (L.unop.image subtype.val) K.unop))],
        apply comp_out.subset_hom, }, },
    { rintro L L' LL',
      simp_rw ←@sec (op ((finset.image subtype.val L.unop) ∪  K.unop : finset _))
                (op ((finset.image subtype.val L'.unop) ∪ K.unop : finset _))
                (op_hom_of_le
                (sup_le_sup_right (finset.image_mono subtype.val (le_of_op_hom LL')) K.unop)),
      apply comp_out_to_local_comp_out_hom, },
  end,
  inv_fun := λ ⟨s,sec⟩, by
  begin
    fsplit,
    fsplit,
    { exact λ L, local_comp_out_to_comp_out G K.unop C _
                   (s (op (L.unop.preimage subtype.val (subtype.val_injective.inj_on _)))), },
    { rintro L L' LL',
      have : op (L.unop.preimage subtype.val ((subtype.val_injective.inj_on _))) ⟶
             op (L'.unop.preimage subtype.val (subtype.val_injective.inj_on _)), by
      { apply op_hom_of_le,
        apply finset.monotone_preimage,
        exact le_of_op_hom LL', },
      rw ←sec this,
      apply local_comp_out_to_comp_out_hom, },
    { apply comp_out.eq_of_not_disjoint,
      rw set.not_disjoint_iff,
      dsimp [local_comp_out_to_comp_out],
      generalize h : s (op (K.unop.preimage subtype.val ((subtype.val_injective.inj_on _))  : finset ↥(C.supp))) = D,
      apply quot.induction_on D,
      rintro ⟨v,h⟩,
      use v,
      simp only [subtype.coe_mk, set_like.coe_mem, and_true, comp_out_mk],
      apply comp_out_mk_mem, },
  end,
  left_inv := λ ⟨⟨s,sec⟩,h⟩, by
  begin
    ext L,
    dsimp [end_comp_out_equiv._match_2, end_comp_out_equiv._match_1],
    generalize h : s L = D,
    revert D,
    refine quot.ind _,
    rintro ⟨v,vnL⟩ hv,
    apply comp_out.eq_of_not_disjoint,
    rw set.not_disjoint_iff,
    dsimp [local_comp_out_to_comp_out, comp_out_to_local_comp_out,
           comp_out_to_option_local_comp_out_some, comp_out_to_option_local_comp_out,
           connected_component.lift_adj, comp_out_mk, connected_component_mk],
    use v,
    split, swap, apply comp_out_mk_mem,
    rw comp_out.mem_supp_iff,
    use vnL,
    sorry,
  end,
  right_inv := by
  begin
    rintro ⟨s,sec⟩,
    ext L,
    generalize h : s L = D,
    revert D,
    refine quot.ind _,
    rintro ⟨⟨v,vC⟩,vnL⟩ hv,
    apply comp_out.eq_of_not_disjoint,
    rw set.not_disjoint_iff,
    use ⟨v,vC⟩,
    dsimp [end_comp_out_equiv._match_2, end_comp_out_equiv._match_1],
    --dsimp [local_comp_out_to_comp_out, comp_out_to_local_comp_out,
    --       comp_out_to_option_local_comp_out_some, comp_out_to_option_local_comp_out],
    split, swap,
    rw hv, apply comp_out_mk_mem,
    dsimp [local_comp_out_to_comp_out],
    sorry,
  end
 }

end simple_graph
