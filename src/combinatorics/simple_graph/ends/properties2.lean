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

variables {V : Type} (G : simple_graph V)


namespace simple_graph

open opposite category_theory classical
local attribute [instance] prop_decidable

protected def connected_component.lift_adj {β : Sort*} (f : V → β)
  (h : ∀ (v w : V), G.adj v w → f v = f w) : G.connected_component → β :=
quot.lift f (λ v w (h' : G.reachable v w), h'.elim $ λ vw, by
  { induction vw, refl, rw ←vw_ih ⟨vw_p⟩, exact h _ _ vw_h, } )

noncomputable abbreviation from_comp {G : simple_graph V} {K : finset V}
  (C : G.comp_out K) (L : finset $ subtype C.supp) : finset V := (L.image subtype.val ∪ K)

private lemma from_comp_mono {G : simple_graph V} {K : finset V}
  (C : G.comp_out K) {L L' : finset $ subtype C.supp}
  (LL' : L ⊆ L') : from_comp C L ⊆ from_comp C L' :=
sup_le_sup_right (finset.image_mono subtype.val LL') K


-- Less tactic'y
noncomputable def comp_out_to_option_local_comp_out (K : finset V)
  (C : G.comp_out K) (L : finset $ subtype C.supp) :
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

lemma comp_out_to_option_local_comp_out_hom (K : finset V) (C : G.comp_out K)
  (L L' : finset $ subtype C.supp) (LL' : L' ⊆ L)
  (D : G.comp_out (from_comp C L)) :
  (G.comp_out_to_option_local_comp_out K C L D).map (comp_out.hom LL') =
   G.comp_out_to_option_local_comp_out K C L' (D.hom $ (from_comp_mono C LL')) :=
begin
  refine quot.induction_on D _,
  rintro ⟨v,hv⟩,
  dsimp [comp_out_to_option_local_comp_out, connected_component.lift_adj, comp_out.hom,
         connected_component.map, connected_component.lift, connected_component_mk],
  split_ifs,
  { refl, },
  { refl, },
end

lemma comp_out_to_option_local_comp_out_some (K : finset V) (C : G.comp_out K)
  (L : finset $ subtype C.supp) :
  ∀ (D : G.comp_out (from_comp C L)) (DC : D.supp ⊆ C),
  ∃ (E : C.coe.comp_out L), G.comp_out_to_option_local_comp_out K C L D = some E :=
begin
  refine quot.ind _,
  rintro ⟨v,hv⟩ DC,
  have : v ∈ C.supp := DC (comp_out_mk_mem G hv),
  dsimp [comp_out_to_option_local_comp_out, connected_component.lift_adj],
  split_ifs,
  exacts [⟨_, rfl⟩, (h this).elim],
end




noncomputable def comp_out_to_local_comp_out  (K : finset V) (C : G.comp_out K)
  (L : finset $ subtype C.supp) (D : G.comp_out (from_comp C L))
  (DC : D.supp ⊆ C) : C.coe.comp_out L :=
(G.comp_out_to_option_local_comp_out_some K C L D DC).some

lemma comp_out_to_local_comp_out_mk (K : finset V)
  (C : G.comp_out K)
  (L : finset $ subtype C.supp)
  (v : C.supp)
  (vnL : v ∈ (↑L : set (C.supp))ᶜ)
  (vnL' : v.val ∈ (↑(from_comp C L) : set V)ᶜ) /- follows from vnL and that `v : C.supp` -/
  (vmkC : (comp_out_mk G vnL').supp ⊆ C) :
  G.comp_out_to_local_comp_out K C L (comp_out_mk G vnL') vmkC = C.coe.comp_out_mk vnL :=
begin
  obtain ⟨v,vC⟩ := v,
  let hE := comp_out_to_option_local_comp_out_some G K C L (comp_out_mk G vnL') vmkC,
  dsimp only [comp_out_to_local_comp_out, comp_out_to_option_local_comp_out, subtype.val_eq_coe,
              subtype.coe_mk, connected_component_mk, comp_out_mk,
              connected_component.lift_adj] at hE ⊢,
  -- Why can't I do `simp [dif_pos vC] at hE ⊢`?
  split_ifs at hE ⊢,
  exact hE.some_spec.symm,
end

lemma comp_out_to_local_comp_out_hom (K : finset V) (C : G.comp_out K)
  (L L' : finset $ subtype C.supp) (LL' : L' ⊆ L)
  (D : G.comp_out (from_comp C L))
  (CD : D.supp ⊆ C) /- this follows from `CD'` -/
  (CD' : (D.hom $ from_comp_mono C LL').supp ⊆ C) :
  (G.comp_out_to_local_comp_out K C L D CD).hom LL' =
   G.comp_out_to_local_comp_out K C L' (D.hom $ from_comp_mono C LL') CD' :=
begin
  have KLL' := from_comp_mono C LL',
  dsimp only [comp_out_to_option_local_comp_out_some, comp_out_to_local_comp_out],
  let := G.comp_out_to_option_local_comp_out_hom K C L L' LL' D,
  rw [(G.comp_out_to_option_local_comp_out_some K C L D CD).some_spec,
      (G.comp_out_to_option_local_comp_out_some K C L' (D.hom $ KLL') CD').some_spec,
      option.map_some'] at this,
  simpa only using this,
end

noncomputable abbreviation to_comp {G : simple_graph V} [decidable_eq V]
  {K : finset V} (C : G.comp_out K)
  (L : finset V) : finset C.supp := L.preimage subtype.val (subtype.val_injective.inj_on _)

lemma from_comp_to_comp_le_union {G : simple_graph V} [decidable_eq V]
  {K : finset V} (C : G.comp_out K) (L : finset V) :
  from_comp C (to_comp C L) ≤ L ∪ K :=
begin
  rintro x,
  simp only [finset.mem_image, set.mem_compl_iff, finset.mem_coe, finset.mem_union,
             finset.mem_preimage, exists_prop, subtype.exists, exists_eq_right_right],
  rintro (⟨_, xL⟩|xK),
  exacts [or.inl xL, or.inr xK],
end

lemma to_comp_from_comp_eq_self {G : simple_graph V} [decidable_eq V]
  {K : finset V} (C : G.comp_out K) (L : finset $ C.supp) : to_comp C (from_comp C L) = L :=
begin
  ext ⟨x,xC⟩,
  simp only [finset.mem_image, set.mem_compl_iff, finset.mem_coe, finset.mem_preimage,
             finset.mem_union, exists_prop, subtype.exists, exists_and_distrib_right,
             exists_eq_right],
  split,
  { rintro (h|xK),
    exacts [h.some_spec, (comp_out.not_mem_of_mem xC xK).elim], },
  { rintro h, left, split, exacts [h, xC], },
end

private lemma to_comp_mono {G : simple_graph V} [decidable_eq V]
  {K : finset V} (C : G.comp_out K)
  {L L' : finset V} (LL' : L ⊆ L') : to_comp C L ⊆ to_comp C L' :=
finset.monotone_preimage (subtype.val_injective) LL'

def local_comp_out_to_comp_out (K : finset V) (C : G.comp_out K) (L : finset V) :
  C.coe.comp_out (to_comp C L) → G.comp_out L :=
connected_component.lift_adj _
  (λ vv, @comp_out_mk _ _ _ vv.val.val
          (by { simpa only [finset.coe_preimage] using subtype.prop vv, }))
  (λ ⟨⟨v,vC⟩,hv⟩ ⟨⟨w,wC⟩,hw⟩ a, by
    { simp only [connected_component.eq],
      apply adj.reachable,
      simpa only [comap_adj, function.embedding.coe_subtype, subtype.coe_mk] using a, })

lemma local_comp_out_to_comp_out_mk (K : finset V)
  (C : G.comp_out K) (L : finset V)
  (v : C.supp)
  (vnL : v.val ∈ (↑L : set V)ᶜ)
  (vnL' : v ∈ (↑(to_comp C L) : set C.supp)ᶜ) :
  G.local_comp_out_to_comp_out K C L (C.coe.comp_out_mk vnL') = G.comp_out_mk vnL := rfl

lemma local_comp_out_to_comp_out_hom (K : finset V) (C : G.comp_out K)
  (L L' : finset V) (h : L' ⊆ L) (D : C.coe.comp_out (to_comp C L)) :
  (local_comp_out_to_comp_out G K C L D).hom h =
  local_comp_out_to_comp_out G K C L' (D.hom $ to_comp_mono C h ) :=
quot.induction_on D (λ _, rfl)


noncomputable abbreviation end_to_local_end (K : (finset V)ᵒᵖ) (C : G.comp_out K.unop) :
  {s : G.end // s.val K = C} → C.coe.end :=
λ sss,
  ⟨ λ L, comp_out_to_local_comp_out G K.unop C _ (sss.val.val (op $ from_comp C L.unop)) $ by
      { obtain ⟨⟨s,sec⟩,rfl⟩ := sss,
        simp_rw ←@sec (op (from_comp _ L.unop)) K
                      (op_hom_of_le (finset.subset_union_right (L.unop.image subtype.val) K.unop)),
        apply comp_out.subset_hom, },
    by
    { obtain ⟨⟨s,sec⟩,rfl⟩ := sss,
      rintro L L' LL',
      simp_rw ←@sec (op (from_comp _ L.unop)) (op (from_comp _ L'.unop))
                    (op_hom_of_le $ from_comp_mono _ $ le_of_op_hom LL'),
      apply comp_out_to_local_comp_out_hom, } ⟩


noncomputable abbreviation local_end_to_end (K : (finset V)ᵒᵖ) (C : G.comp_out K.unop) :
  C.coe.end → {s : G.end // s.val K = C} :=
λ ss,
  ⟨ ⟨ λ L, local_comp_out_to_comp_out G K.unop C _ (ss.val (op (to_comp C L.unop))),
      by
      { rintro L L' LL',
        have : op (to_comp C L.unop) ⟶ op (to_comp C L'.unop) :=
          op_hom_of_le (to_comp_mono _ $ le_of_op_hom LL'),
        simp_rw [subtype.val_eq_coe, ←ss.prop this],
        apply local_comp_out_to_comp_out_hom, }⟩,
    by
    { obtain ⟨s,sec⟩ := ss,
      obtain ⟨v,h⟩ := (s (op (to_comp C K.unop))).nonempty,
      obtain ⟨vK,h'⟩ := comp_out.mem_supp_iff.mp h,
      dsimp at h' ⊢,
      apply comp_out.eq_of_not_disjoint,
      rw [set.not_disjoint_iff, ←h', local_comp_out_to_comp_out_mk], swap,
      { simpa using comp_out.not_mem_of_mem v.prop, },
      exact ⟨v.val, comp_out_mk_mem _ _, v.prop⟩, }⟩

lemma single_use {V : Type}
  {G : simple_graph V}
  [decidable_eq V]
  {K : (finset V)ᵒᵖ}
  {C : G.comp_out ↑(unop K)}
  {s : Π (j : (finset ↥(C.supp))ᵒᵖ), C.coe.comp_out_functor.obj j}
  {sec : s ∈ C.coe.end}
  {L : (finset ↥(C.supp))ᵒᵖ}
  {M : (finset ↥(C.supp))ᵒᵖ}
  (this : L = M)
  {v : ↥(C.supp)}
  (h : v ∈ (s L).supp)
  (vnL : v ∈ (↑L.unop : set C.supp)ᶜ) :
  C.coe.comp_out_mk vnL = s L ↔ C.coe.comp_out_mk (this.rec_on vnL) = s M :=
begin
  cases this,
  refl,
end

noncomputable def equiv_local_end (K : (finset V)ᵒᵖ) (C : G.comp_out K.unop) :
  {s : G.end // s.val K = C} ≃ C.coe.end :=
{ to_fun := end_to_local_end G K C,
  inv_fun := local_end_to_end G K C,
  left_inv := by
  begin
    rintro ⟨⟨s,sec⟩,rfl⟩,
    simp only [subtype.mk_eq_mk],
    ext L,
    let LK := op (L.unop ∪ K.unop),
    obtain ⟨v,h⟩ := (s LK).nonempty,
    obtain ⟨vnLK,vsLK⟩ := comp_out.mem_supp_iff.mp h,
    dsimp,
    have h₁ : LK ⟶ (op $ from_comp (s K) (to_comp (s K) L.unop)), by
    { apply op_hom_of_le, apply from_comp_to_comp_le_union, },
    have h₂ : LK ⟶ L, by { apply op_hom_of_le, exact le_sup_left, },
    have h₃ : LK ⟶ K, by { apply op_hom_of_le, exact le_sup_right, },
    have k₁ := end_hom_mk_of_mk G ((λ _ _ f, sec f) : s ∈ G.end) h₁ vnLK vsLK.symm, dsimp at k₁,
    have k₂ := end_hom_mk_of_mk G ((λ _ _ f, sec f) : s ∈ G.end) h₂ vnLK vsLK.symm, dsimp at k₂,
    have k₃ := end_hom_mk_of_mk G ((λ _ _ f, sec f) : s ∈ G.end) h₃ vnLK vsLK.symm, dsimp at k₃,
    -- I can't group the `rw` and `simp_rw`…
    simp_rw [k₁, k₂],
    rw [G.comp_out_to_local_comp_out_mk K.unop (s K) (to_comp (s K) L.unop) ⟨v,_⟩ _ _ _,
        G.local_comp_out_to_comp_out_mk],
    { simp only [k₃, set.mem_compl_iff, finset.mem_coe, set.mem_set_of_eq,
                 connected_component.eq, unop_op, finset.coe_union, set.compl_union,
                 set.mem_inter_iff] at vnLK ⊢,
      exact ⟨vnLK.right, reachable.refl _⟩, },
    { simp only [finset.coe_preimage, set.mem_compl_iff, set.mem_preimage, finset.mem_coe,
                 unop_op, finset.coe_union, set.compl_union, set.mem_inter_iff] at vnLK ⊢,
      exact vnLK.left, },
  end,
  right_inv := by
  begin
    rintro ⟨s,sec⟩,
    simp only [subtype.mk_eq_mk],
    ext L,
    dsimp,
    have : op (to_comp C (from_comp C (unop L))) = L, by
    { rw op_eq_iff_eq_unop,
      apply to_comp_from_comp_eq_self, },
    obtain ⟨v,h⟩ := (s (op $ to_comp C (from_comp C (unop L)))).nonempty,
    obtain ⟨vnL,vsL⟩ := comp_out.mem_supp_iff.mp h,
    simp_rw [←vsL,
             G.local_comp_out_to_comp_out_mk _ _ (from_comp C L.unop) v (by simpa using vnL) vnL,
             G.comp_out_to_local_comp_out_mk K.unop C L.unop v (this ▸ vnL)],
    rw ←single_use this h vnL, exact vsL, exact (λ _ _ f, sec f),
    -- kind of ugly but don't know how to do it better :
    -- convert vsL; exact this.symm,
  end }

end simple_graph
