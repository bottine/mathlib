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

noncomputable def comp_out_to_option_local_comp_out [decidable_eq V] (K : set V) (C : G.comp_out K)
  (L : set $ subtype C.subgraph.verts) :
  ∀ (D : G.comp_out ((L.image subtype.val) ∪ K)), option (C.subgraph.coe.comp_out L) :=
begin
  fapply connected_component.lift_adj,
  { rintro vv,
    by_cases vC : vv.val ∈ C,
    { apply some,
      apply @comp_out_mk _ _ C.subgraph.coe ⟨vv.val, vC⟩ _,
      obtain ⟨v,h⟩ := vv,
      simp only [subgraph.induce_verts, set.compl_union, set.mem_inter_iff, set.mem_compl_iff,
                 set.mem_image, subtype.exists, exists_and_distrib_right, exists_eq_right,
                 not_exists] at h,
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
    { exact (hwC (comp_out.mem_of_adj v w hvC (λ wK, hw (or.inr wK)) a)).elim, },
    { exact (hvC (comp_out.mem_of_adj w v hwC (λ vK, hv (or.inr vK)) a.symm)).elim, },
    { refl, }, },
end

lemma comp_out_to_option_local_comp_out_hom [decidable_eq V] (K : set V) (C : G.comp_out K)
  (L L' : set $ subtype C.subgraph.verts) (LL' : L' ⊆ L)
  (KLL' : (L'.image subtype.val) ∪ K ⊆ (L.image subtype.val) ∪ K) -- this follows from `LL'`
  (D : G.comp_out ((L.image subtype.val) ∪ K)) :
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

lemma comp_out_to_option_local_comp_out_some [decidable_eq V] (K : set V) (C : G.comp_out K)
  (L : set $ subtype C.subgraph.verts) :
  ∀ (D : G.comp_out ((L.image subtype.val) ∪ K)) (DC : D.supp ⊆ C),
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

noncomputable def comp_out_to_local_comp_out  [decidable_eq V] (K : set V) (C : G.comp_out K)
  (L : set $ subtype C.subgraph.verts) (D : G.comp_out ((L.image subtype.val) ∪ K))
  (DC : D.supp ⊆ C) : C.subgraph.coe.comp_out L :=
(G.comp_out_to_option_local_comp_out_some K C L D DC).some

lemma comp_out_to_local_comp_out_hom [decidable_eq V] (K : set V) (C : G.comp_out K)
  (L L' : set $ subtype C.subgraph.verts) (LL' : L' ⊆ L)
  (D : G.comp_out ((L.image subtype.val) ∪ K))
  (KLL' : (L'.image subtype.val) ∪ K ⊆ (L.image subtype.val) ∪ K) -- this follows from `LL'`
  (CD : D.supp ⊆ C)  -- this follows from `CD'`
  (CD' : (D.hom KLL').supp ⊆ C) :
  (G.comp_out_to_local_comp_out K C L D CD).hom LL' =
   G.comp_out_to_local_comp_out K C L' (D.hom $ KLL') CD' :=
begin
  dsimp only [comp_out_to_option_local_comp_out_some, comp_out_to_local_comp_out],
  let := G.comp_out_to_option_local_comp_out_hom K C L L' LL' KLL' D,
  rw [(G.comp_out_to_option_local_comp_out_some K C L D CD).some_spec,
      (G.comp_out_to_option_local_comp_out_some K C L' (D.hom $ KLL') CD').some_spec,
      option.map_some'] at this,
  simpa using this,
end

def local_comp_out_to_comp_out [decidable_eq V] (K : set V) (C : G.comp_out K) (L : set V) :
  C.subgraph.coe.comp_out (L.preimage subtype.val) → G.comp_out L :=
begin
  fapply connected_component.lift_adj,
  rintro ⟨⟨v,vC⟩,hv⟩,
  fapply comp_out_mk,
  { exact v, },
  { simpa using hv, }
end

lemma local_comp_out_to_comp_out_hom [decidable_eq V] (K : set V) (C : G.comp_out K)
  (L L' : set V) (h : L' ⊆ L) (D):
  (local_comp_out_to_comp_out G K C L D).hom h =
  local_comp_out_to_comp_out G K C L' (D.hom $ set.preimage_mono h) := sorry

/-
noncomputable def end_to_local_end₀ [decidable_eq V] (K : (finset V)ᵒᵖ) (s : G.end)
  (L : finset $ subtype (s.val K).subgraph.verts) : (s.val K).subgraph.coe.comp_out L :=
let
  L' := L.image (subtype.val),
  vvLK := (s.val (opposite.op (L' ∪ K.unop))).nonempty,
  v := vvLK.some,
  hvLK := vvLK.some_spec,
  vsK : v ∈ (s.val K).supp :=
    set.mem_of_mem_of_subset hvLK
      ((comp_out.hom_eq_iff_le _ _ _).mp
        (s.prop (category_theory.op_hom_of_le (finset.subset_union_right _ _))))
in
  @comp_out_mk _ _ ((s.val K).subgraph.coe)
                    ⟨(s.val (opposite.op (L' ∪ K.unop))).nonempty.some, vsK⟩ $ by
  begin
    let := comp_out.not_mem_of_mem hvLK,
    simp_rw [opposite.unop_op, finset.mem_coe, finset.mem_union, not_or_distrib,
              finset.mem_image] at this,
    exact λ h, this.left ⟨⟨v,vsK⟩, ⟨h,rfl⟩⟩,
  end

lemma end_to_local_end₀_agree [decidable_eq V] (K : (finset V)ᵒᵖ) (s : G.end)
  (L : finset $ subtype (s.val K).subgraph.verts) :
  (s.val (opposite.op ((L.image subtype.val) ∪ K.unop))).supp.preimage subtype.val =
  (end_to_local_end₀ G K s L).supp := sorry


noncomputable def end_to_local_end [decidable_eq V] (K : (finset V)ᵒᵖ) (s : G.end) :
  (s.val K).subgraph.coe.end :=
⟨ λ L, end_to_local_end₀ G K s L.unop,
  by
  { rintro L L' LL',
    simp,
    dsimp [comp_out_functor],
    rw comp_out.hom_eq_iff_le,
    simp only [coe, lift_t, has_lift_t.lift, coe_t, has_coe_t.coe, set_like.coe],
    rw ←end_to_local_end₀_agree,
    rw ←end_to_local_end₀_agree,
    apply set.preimage_mono,
    suffices: ↑(s.val (opposite.op (finset.image subtype.val (opposite.unop L) ∪ opposite.unop K))) ⊆
           ↑(s.val (opposite.op (finset.image subtype.val (opposite.unop L') ∪ opposite.unop K))),
    { sorry, },
    rw ←comp_out.hom_eq_iff_le,
    apply s.prop, apply category_theory.op_hom_of_le,
    simp, sorry,
    } ⟩


noncomputable def end_of_local_end [decidable_eq V] {K : (finset V)ᵒᵖ} {C : G.comp_out K.unop}
  (s : C.subgraph.coe.end) : G.end :=
⟨ λ L,
    let
      L' := L.unop.preimage (subtype.val : C.subgraph.verts → V) (subtype.val_injective.inj_on _),
      CL':= s.val (opposite.op L'),
      vCL' := CL'.nonempty
    in
      @comp_out_mk _ _ G vCL'.some.val $ by
      begin
        convert comp_out.not_mem_of_mem vCL'.some_spec,
        simp only [set.mem_compl_iff, finset.mem_coe, opposite.unop_op, finset.mem_preimage,
                   subtype.val_eq_coe], refl
      end,
  λ L M LM, by
    begin
      /-simp only [subtype.val_eq_coe],
      apply comp_out.eq_of_not_disjoint,
      rw set.not_disjoint_iff,
      let L' := L.unop.preimage (subtype.val : C.subgraph.verts → V) (subtype.val_injective.inj_on _),
      let CL':= s.val (opposite.op L'),
      let vCL' := CL'.nonempty,
      let M' := M.unop.preimage (subtype.val : C.subgraph.verts → V) (subtype.val_injective.inj_on _),
      let CM':= s.val (opposite.op M'),
      let vCM' := CM'.nonempty,
      have LM' : M' ≤ L', by {
        apply finset.monotone_preimage,
        exact category_theory.le_of_op_hom LM,},
      rw ←opposite.unop_op M' at LM',
      rw ←opposite.unop_op L' at LM',
      have := s.prop (category_theory.op_hom_of_le LM'),
      dsimp only [comp_out_functor] at this,
      rw comp_out.hom_eq_iff_le at this,
      use vCL'.some.val,
      --rw comp_out.mem_supp_iff.mp vCM'.some_spec at this,-/
      sorry,
    end ⟩

lemma  end_of_local_end_agree [decidable_eq V] {K : (finset V)ᵒᵖ} {C : G.comp_out K.unop}
  (s : C.subgraph.coe.end) : (end_of_local_end G s).val K = C := sorry

noncomputable def end_comp_out_equiv [decidable_eq V] (K : (finset V)ᵒᵖ) (C : G.comp_out K.unop) :
  {s : G.end // s.val K = C} ≃ C.subgraph.coe.end :=
{ to_fun := λ s, by { rw ←s.prop, exact (end_to_local_end G K s.val), },
  inv_fun := λ s, ⟨end_of_local_end G s, end_of_local_end_agree G s⟩,
  left_inv := λ s, by
  begin
    ext L,
    obtain ⟨⟨s, sec⟩,h⟩ := s,
    simp only [eq_mpr_eq_cast, subtype.coe_mk],
    apply comp_out.eq_of_not_disjoint,
    rw set.not_disjoint_iff,
    let L' := L.unop.preimage (subtype.val : C.subgraph.verts → V) (subtype.val_injective.inj_on _),
    cases h,
    simp only [cast_eq],
    simp only [set.mem_compl_iff, finset.mem_coe, cast_eq, set_like.mem_coe],
    let CL':= s L,
    let vCL' := CL'.nonempty,
    use vCL'.some,
    refine ⟨_, vCL'.some_spec⟩,
    dsimp [end_of_local_end, end_to_local_end],
  end
 }
-/

-/
end simple_graph
