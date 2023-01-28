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

private abbreviation from_comp {G : simple_graph V} [decidable_eq V] {K : finset V}
  (C : G.comp_out K) (L : finset $ subtype C.supp) : finset V := (L.image subtype.val ∪ K)

noncomputable def comp_out_to_option_local_comp_out [decidable_eq V] (K : finset V)
  (C : G.comp_out K) (L : finset $ subtype C.supp) :
  ∀ (D : G.comp_out (from_comp C L)), option (C.coe.comp_out L) :=
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
      exact or.inl ⟨vC, vL⟩, },
    { exact none, } },
  { rintro ⟨v,hv⟩ ⟨w,hw⟩ a,
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
  (KLL' : from_comp C L' ⊆ from_comp C L) -- this follows from `LL'`
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
  ∀ (D : G.comp_out (from_comp C L)) (DC : D.supp ⊆ C),
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
  (L : finset $ subtype C.supp) (D : G.comp_out (from_comp C L))
  (DC : D.supp ⊆ C) : C.coe.comp_out L :=
(G.comp_out_to_option_local_comp_out_some K C L D DC).some

lemma comp_out_to_local_comp_out_eq_of_mem [decidable_eq V] (K : finset V)
  (C : G.comp_out K)
  (L : finset $ subtype C.supp)
  (D : G.comp_out ((L.image subtype.val) ∪ K : finset _))
  (DC : D.supp ⊆ C)
  (v : V)
  (vD : v ∈ D)
  (vnL : (⟨v, DC vD⟩ : C.supp) ∉ L) /- follows from vD -/ :
  G.comp_out_to_local_comp_out K C L D DC = @comp_out_mk C.supp L C.coe ⟨v,DC vD⟩ (vnL) :=
begin
  classical,
  rw comp_out.mem_supp_iff at vD,
  obtain ⟨vnLK, rfl⟩ := vD,
  let hE := comp_out_to_option_local_comp_out_some G K C L _ DC,
  dsimp only [comp_out_to_local_comp_out, comp_out_to_option_local_comp_out, subtype.val_eq_coe,
              subtype.coe_mk, connected_component_mk, comp_out_mk,
              connected_component.lift_adj] at hE ⊢,
  split_ifs at hE ⊢,
  { exact hE.some_spec.symm, },
  { exfalso, exact h (DC vD), },
end

lemma comp_out_to_local_comp_out_hom [decidable_eq V] (K : finset V) (C : G.comp_out K)
  (L L' : finset $ subtype C.supp) (LL' : L' ⊆ L)
  (D : G.comp_out ((L.image subtype.val) ∪ K : finset _))
  (CD : D.supp ⊆ C)  -- this follows from `CD'`
  (KLL' : from_comp C L' ⊆ from_comp C L) -- this follows from `LL'`
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

private noncomputable abbreviation to_comp {G : simple_graph V} [decidable_eq V]
  {K : finset V} (C : G.comp_out K)
  (L : finset V) : finset C.supp := L.preimage subtype.val (subtype.val_injective.inj_on _)

def local_comp_out_to_comp_out [decidable_eq V] (K : finset V) (C : G.comp_out K) (L : finset V) :
  C.coe.comp_out (to_comp C L) → G.comp_out L :=
connected_component.lift_adj _
  (λ vv, @comp_out_mk _ _ _ vv.val.val
          (by { simpa only [finset.coe_preimage] using subtype.prop vv, }))
  (λ ⟨⟨v,vC⟩,hv⟩ ⟨⟨w,wC⟩,hw⟩ a, by
    { simp only [connected_component.eq],
      apply adj.reachable,
      simpa only [comap_adj, function.embedding.coe_subtype, subtype.coe_mk] using a, })

lemma local_comp_out_to_comp_out_hom [decidable_eq V] (K : finset V) (C : G.comp_out K)
  (L L' : finset V) (h : L' ⊆ L) (D : C.coe.comp_out (to_comp C L)) :
  (local_comp_out_to_comp_out G K C L D).hom h =
  local_comp_out_to_comp_out G K C L' (D.hom $ finset.monotone_preimage subtype.val_injective h ) :=
quot.induction_on D (λ _, rfl)

noncomputable def end_comp_out_equiv [decidable_eq V] (K : (finset V)ᵒᵖ) (C : G.comp_out K.unop) :
  {s : G.end // s.val K = C} ≃ C.coe.end :=
{ to_fun := λ sss,
  ⟨ λ L, comp_out_to_local_comp_out G K.unop C _ (sss.val.val (op $ from_comp C L.unop)) $ by
      { obtain ⟨⟨s,sec⟩,rfl⟩ := sss,
        simp_rw [←@sec (op (from_comp _ L.unop)) K
                      (op_hom_of_le (finset.subset_union_right (L.unop.image subtype.val) K.unop))],
        apply comp_out.subset_hom, },
    by
    { obtain ⟨⟨s,sec⟩,rfl⟩ := sss,
      rintro L L' LL',
      simp_rw ←@sec (op (from_comp _ L.unop))
                (op (from_comp _ L'.unop))
                (op_hom_of_le
                (sup_le_sup_right (finset.image_mono subtype.val (le_of_op_hom LL')) K.unop)),
      apply comp_out_to_local_comp_out_hom, } ⟩,
  inv_fun := λ ss,
  ⟨ ⟨ λ L, local_comp_out_to_comp_out G K.unop C _ (ss.val (op (to_comp C L.unop))),
      by
      { rintro L L' LL',
        have : op (to_comp C L.unop) ⟶ op (to_comp C L'.unop) :=
          op_hom_of_le (finset.monotone_preimage subtype.val_injective (le_of_op_hom LL')),
        simp_rw [subtype.val_eq_coe,←ss.prop this],
        apply local_comp_out_to_comp_out_hom, }⟩,
    by
    { obtain ⟨s,sec⟩ := ss,
      apply comp_out.eq_of_not_disjoint,
      rw set.not_disjoint_iff,
      dsimp [local_comp_out_to_comp_out],
      generalize h : s (op (to_comp C K.unop)) = D,
      apply quot.induction_on D,
      rintro ⟨v,h⟩,
      use v,
      simp only [subtype.coe_mk, set_like.coe_mem, and_true, comp_out_mk],
      apply comp_out_mk_mem, }⟩,
  left_inv := λ ⟨⟨s,sec⟩,h⟩, by
  begin
  -- Probably we need to take `L ∪ K` at some point, which I haven't done

    ext L,
    generalize h : s L = D,
    revert D,
    refine quot.ind _,
    rintro ⟨v,vnL⟩ hv,
    apply comp_out.eq_of_not_disjoint,
    rw set.not_disjoint_iff,
    dsimp [local_comp_out_to_comp_out,
           comp_out_to_option_local_comp_out_some, comp_out_to_option_local_comp_out,
           connected_component.lift_adj, comp_out_mk, connected_component_mk],
    use v,
    split, swap, apply comp_out_mk_mem,
    rw comp_out.mem_supp_iff,
    use vnL,
    rw G.comp_out_to_local_comp_out_eq_of_mem (unop K) C ((unop L).preimage subtype.val _)
       (s (op (finset.image subtype.val ((unop L).preimage subtype.val _) ∪ unop K))) _ v,
    rotate,
    { simp only [finset.mem_preimage], exact vnL, },
    { have : op (finset.image subtype.val ((unop L).preimage subtype.val (subtype.val_injective.inj_on _)) ∪ unop K) ⟶ L, by
        sorry,


    },

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
    --dsimp [local_comp_out_to_comp_out, comp_out_to_local_comp_out,
    --       comp_out_to_option_local_comp_out_some, comp_out_to_option_local_comp_out],
    split, swap,
    rw hv, apply comp_out_mk_mem,
    dsimp [local_comp_out_to_comp_out, connected_component.lift_adj, connected_component.lift,
           comp_out_mk, connected_component_mk],

    --rw comp_out.mem_supp_iff,
    --use vnL,
    rw G.comp_out_to_local_comp_out_eq_of_mem (K.unop) C (L.unop) _ _ v _ _,
    rotate,
    { simp, }


    sorry,
  end}


end simple_graph
