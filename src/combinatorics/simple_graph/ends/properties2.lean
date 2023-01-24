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

-- set_option profiler true

variables {V : Type} (G : simple_graph V)

namespace simple_graph

protected def connected_component.lift_adj {β : Sort*} (f : V → β)
  (h : ∀ (v w : V), G.adj v w → f v = f w) : G.connected_component → β :=
quot.lift f (λ v w (h' : G.reachable v w), h'.elim $ λ vw, by
  { induction vw, refl, rw ←vw_ih ⟨vw_p⟩, exact h _ _ vw_h, } )


protected def rec' {β : G.connected_component → Sort*}
  (f : Π a, β (G.connected_component_mk a))
  (h : ∀ (a b : V) (p : G.reachable a b),
         ( (quot.sound p).rec_on (f a) : β (quot.mk G.reachable b)) = f b)
  (q : G.connected_component) : β q :=
eq.rec_on (quot.lift_indep_pr1 f h q) ((quot.lift (quot.indep f) (quot.indep_coherent f h) q).2)


protected def rec'' {β : G.connected_component → Sort*}
  (f : Π a, β (G.connected_component_mk a))
  (h : ∀ (a b : V) (p : G.adj a b),
         ((quot.sound p.reachable).rec_on (f a) : β (quot.mk G.reachable b)) = f b)
  (q : G.connected_component) : β q :=
begin
  fapply simple_graph.rec',
  exact f,
  rintro a b ⟨p⟩,
  induction p,
  { refl, },
  { specialize h _ _ p_h,
    rw [←p_ih, ←h],
    -- rw eq_rec_compose _ _ (f p_u),
    finish, /- magic -/
    },
end

def comp_out_to_local_comp_out [decidable_eq V] {G : simple_graph V} (K : set V) (C : G.comp_out K)
  (L : set $ subtype C.subgraph.verts) :
  ∀ (D : G.comp_out ((L.image subtype.val) ∪ K)), D.supp ⊆ C → C.subgraph.coe.comp_out L :=
  --  simple_graph.rec'' C.subgraph.coe
  --   (λ v, _)
  --   _
begin
  refine simple_graph.rec'' _ _ _,
  { rintro v vC,
    let v' : ↥(C.subgraph.verts) := ⟨v, vC ⟨v.property, congr_arg _ (subtype.ext_val (eq.refl v.val))⟩⟩,
    have : v' ∈ Lᶜ := by {
      intro h,
      apply v.property,
      left,
      exact set.mem_image_of_mem subtype.val h,
    },
    exact comp_out_mk C.subgraph.coe this,
  },
  { rintro u v uv,
    let h := (quot.sound uv.reachable),
    sorry
   }
end

/-
lemma comp_out_to_local_comp_out_hom [decidable_eq V] (K : set V) (C : G.comp_out K)
  (L L' : set $ subtype C.subgraph.verts) (LL' : L' ⊆ L) (D : G.comp_out ((L.image subtype.val) ∪ K))
  (KLL' : (L'.image subtype.val) ∪ K ⊆ (L.image subtype.val) ∪ K) (CD : (D.hom KLL').supp ⊆ C) :
  (comp_out_to_local_comp_out K C L D $ (D.subset_hom KLL').trans CD).hom LL' =
  comp_out_to_local_comp_out K C L' (D.hom $ KLL') CD :=
begin
  apply comp_out.eq_of_not_disjoint,
  rw set.not_disjoint_iff,
  let v := D.nonempty.some,
  have vD : v ∈ D.supp := D.nonempty.some_spec,
  have vC : v ∈ C.supp := CD ((comp_out.subset_hom _ _) vD),
  use ⟨v, vC⟩,
  split,
  { apply set.mem_of_mem_of_subset _ (comp_out.subset_hom _ _),
    -- TODO: Debug
    -- apply comp_out_mk_mem,
    sorry
     },
  { let D' := D.hom KLL',
    apply comp_out.mem_supp_iff.mpr,
    dsimp [comp_out_to_local_comp_out],
    fsplit,
    { sorry, },
    { sorry {let v' := D'.nonempty.some,
      let vD' : v' ∈ D' := D'.nonempty.some_spec,
      dsimp [comp_out_mk],
      -- simp only [connected_component.eq],
      change (C.subgraph.coe.out L').reachable ⟨⟨v, vC⟩, _⟩ ⟨⟨v', _⟩, _⟩,
      have : v ∈ D'.supp := set.mem_of_mem_of_subset vD (D.subset_hom KLL'),
      change v ∈ D' at this, rw comp_out.mem_supp_iff at this,
      rw comp_out.mem_supp_iff at vD',
      have lol := this.some_spec.trans vD'.some_spec.symm,
      simp only [connected_component.eq] at lol,
      obtain ⟨p⟩ := lol,
      revert v v',
      induction p,
      { simp at *, },
      }
    }
   },


 end

def local_comp_out_to_comp_out [decidable_eq V] (K : set V) (C : G.comp_out K) (L : set V) :
  C.subgraph.coe.comp_out (L.preimage subtype.val) → G.comp_out L :=
begin
  fapply connected_component.lift_adj,
  rintro ⟨⟨v,vC⟩,hv⟩,
  fapply comp_out_mk,
  { exact v, },
  { simpa using hv, },
  sorry
end

lemma local_comp_out_to_comp_out_hom [decidable_eq V] (K : set V) (C : G.comp_out K)
  (L L' : set V) (h : L' ⊆ L) (D):
  (local_comp_out_to_comp_out G K C L D).hom h =
  local_comp_out_to_comp_out G K C L' (D.hom $ set.preimage_mono h) := sorry
-/

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
end simple_graph
