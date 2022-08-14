import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition
import combinatorics.simple_graph.prod
import .mathlib
import .reachable_outside
import .end_limit_construction

open function
open finset
open set
open classical
open simple_graph.walk
open relation

universes u v w



noncomputable theory
local attribute [instance] prop_decidable

namespace simple_graph


variables  {V : Type u}
           (G : simple_graph V)
           (Gpc: G.preconnected)
          [locally_finite G]
           {V' : Type v}
           (G' : simple_graph V')
           {V'' : Type w}
           (G'' : simple_graph V'')


namespace ends

open ro_component
open simple_graph


section finite

-- Locally_finite follows from finiteness
lemma no_end_of_finite_graph  (Gpc: G.preconnected) [locally_finite G] (Vfinite : (@set.univ V).finite) : (Ends G Gpc) ≃ empty :=
begin
  transitivity,
  exact Ends_equiv_Endsinfty G Gpc,
  apply @equiv.equiv_empty _ _,
  apply is_empty.mk,
  rintros ⟨f,f_comm⟩,
  obtain ⟨⟨C,Ccomp⟩,Cinf⟩ := f (set.finite.to_finset Vfinite),
  exact Cinf (set.finite.subset Vfinite (set.subset_univ C)),
end

end finite


section infinite

lemma end_of_infinite_graph (Vinf : set.infinite  (@set.univ V)) : (Ends G Gpc).nonempty :=
  @inverse_system.nonempty_sections_of_fintype_inverse_system' _ _ _ (ComplComp G Gpc) _ (ComplComp_nonempty G Gpc Vinf)

end infinite


section nat

def gℕ : simple_graph ℕ := simple_graph.from_rel (λ n m, m = n.succ)

instance gℕlf : locally_finite gℕ := sorry
lemma gℕpc : gℕ.preconnected := sorry

lemma gt_subconnected (m : ℕ) : subconnected gℕ {n : ℕ | n > m} := by {
  let L := {n : ℕ | n > m},
  rintros x xm y ym,
  wlog h : x ≤ y using [x y, y x],
  { exact le_total x y, },
  { rcases le_iff_exists_add.mp h with ⟨z,rfl⟩,
    induction z,
    { use nil,simp, exact ym, },
    { simp only [gt_iff_lt, mem_set_of_eq] at xm,
      rcases z_ih (le_self_add) ( by { simp, exact lt_of_lt_of_le xm (by simp) } ) with ⟨w,wgood⟩,
      let w' := w.append (cons ((from_rel_adj _ (x+z_n) (x+z_n).succ).mpr ⟨(x + z_n).succ_ne_self.symm,or.inl rfl⟩) nil),
      use w',
      rw walk.support_append,
      rw list.to_finset_append,
      simp,
      rw set.insert_subset,
      split,
      { exact lt_of_lt_of_le xm h, },
      { exact wgood },
    }, -- todo
  },
  { rcases this ym xm with ⟨w,wgood⟩,
    use w.reverse,
    rw walk.support_reverse,
    rw list.to_finset_reverse,
    exact wgood,
  },
}


lemma ends_nat : (Ends gℕ gℕpc) ≃ unit :=
begin


  suffices H : ∀ K : finset ℕ, ∃ D : set ℕ, disjoint D K ∧ subconnected gℕ D ∧ D.infinite ∧ (D ᶜ).finite,
  {
    obtain ⟨dis,conn,inf,cof⟩ := (H ∅).some_spec,
    have : (ComplInfComp gℕ gℕpc).obj ∅ ≃ unit, from
    cofinite_inf_ro_component_equiv'' gℕ gℕpc ∅ _ dis conn inf cof,
    transitivity, exact (Ends_equiv_Endsinfty gℕ gℕpc),
    transitivity, rotate, exact this,


    -- Shitty unneeded instance that we should remove in the assumptions of
    -- `Endsinfty_eventually constant`
    haveI : ∀ (L : finset ℕ), nonempty ((ComplComp gℕ gℕpc).obj L), by {
      rintro L,
      obtain ⟨dis,conn,inf,cof⟩ := (H L).some_spec,
      let C := (ro_component.of_subconnected_disjoint gℕ L (H L).some (set.infinite.nonempty inf) dis conn).some,
      obtain ⟨Ccomp,DC⟩ := (ro_component.of_subconnected_disjoint gℕ L (H L).some (set.infinite.nonempty inf) dis conn).some_spec,
      apply nonempty.intro,
      exact ⟨C,Ccomp⟩,
    },

    apply @Endsinfty_eventually_constant _ _ gℕ gℕpc _ _ ∅,
    rintro L LL,
    transitivity, rotate, exact this.symm,
    obtain ⟨dis,conn,inf,cof⟩ := (H L).some_spec,
    exact cofinite_inf_ro_component_equiv'' gℕ gℕpc L _ dis conn inf cof,
  },


  intro K,
  have : ∃ m : ℕ, ∀ k ∈ K, m ≥ k, by
  { by_cases h : K.nonempty,
    { let m := K.max,
      rcases finset.max_of_nonempty h with ⟨a,e⟩,
      use a,
      rintro k kK,
      simp,
      exact le_max_of_mem kK e,},
    {use 0,rintro k kK,exfalso, simp at h, rw h at kK,simp at kK, exact kK,},},

  rcases this with ⟨m,mtop⟩,
  let L := {n : ℕ | n > m },
  have Ldis : disjoint L K, by { rw set.disjoint_iff, rintro x ⟨xL,xK⟩, simp at xL, simp, specialize mtop x xK, simp at mtop, exact (not_le_of_lt xL) mtop, },
  have Lcof : (L ᶜ).finite, by {dsimp [compl,boolean_algebra.compl],simp, apply set.finite_le_nat},
  -- There is no set.infinite_gt_nat ??
  have Linf : L.infinite, by {apply set.infinite_of_finite_compl,exact Lcof, },
  have Lconn := gt_subconnected m,

  use [L,Ldis,Lconn,Linf,Lcof],
end

end nat

-- Commented because it makes lean lag, but will need to be included and corrected again
/-
section product


private lemma finprod_compl_subconnected [Vnempty : nonempty V] [Vnempty' : nonempty V']
  [locally_finite G] [locally_finite G']
  (Gpc :G.preconnected) (Gpc' : G'.preconnected)
  (Vinf : set.infinite (@set.univ V)) (V'inf : set.infinite (@set.univ V'))
  (K : finset V) (K' : finset V') :
  subconnected (G □ G') ((finset.product K K' : set (V × V') )ᶜ) :=
begin
  let VV := V × V',
  let GG := G □ G',
  let L := finset.product K K',
  let D := (L :set (V × V')) ᶜ,

  have memD_iff : ∀ x : VV, x ∈ D ↔ x.1 ∉ K ∨ x.2 ∉ K', by
  { rintro x,
    rw ←not_iff_not,
    push_neg,
    rw set.mem_compl_iff,
    simp,},

  -- V is infinite, K is finite
  let k : V, by sorry,
  let kK : k ∉ K, by sorry,
  let k' : V', by sorry,
  let kK' : k' ∉ K', by sorry,

  rintros ⟨x,x'⟩ xinD ⟨y,y'⟩ yinD,

  have :(∃ (z z': VV)
          (u : GG.walk ⟨x,x'⟩ z)
          (v : GG.walk z z')
          (w : GG.walk z' ⟨y,y'⟩),
          (u.support.to_finset : set VV) ⊆ D
        ∧ (v.support.to_finset : set VV) ⊆ D
        ∧ (w.support.to_finset : set VV) ⊆ D), by
  { have : ∀ x ∉ K,
            ∀ {y y' : V'} (w : G'.walk y y'), ((walk.box_prod_right G x w).support.to_finset : set VV) ⊆ D, by {
      rintros x xnotin y y' w,
      rw simple_graph.walk.support_box_prod_right,
      rw list.map_to_finset,
      rintro p q,
      simp at q,
      rcases q with ⟨v,⟨vin,rfl⟩⟩,
      apply (memD_iff ⟨x,v⟩).mpr,
      left, exact xnotin,},

    have : ∀ x ∉ K',
            ∀ {y y' : V} (w : G.walk y y'), ((walk.box_prod_left G' x w).support.to_finset : set VV) ⊆ D, by
    { rintros x xnotin y y' w,
      rw simple_graph.walk.support_box_prod_left,
      rw list.map_to_finset,
      rintro p q,
      simp at q,
      rcases q with ⟨v,⟨vin,rfl⟩⟩,
      apply (memD_iff ⟨v,x⟩).mpr,
      right, exact xnotin,},

    rcases (memD_iff ⟨x,x'⟩).mp xinD with xnot|xnot',
    { rcases (memD_iff ⟨y,y'⟩).mp yinD with ynot|ynot',
      { -- pffh too much woooork
        -- we need in some cases to make use of k or k' defined above.
        -- That's why we need a concatenation of three paths and not just two.
        sorry,
      },
      { sorry },
    },
    { rcases (memD_iff ⟨y,y'⟩).mp yinD with ynot|ynot',
      { sorry },
      { sorry },
    }

  },

  rcases this with ⟨z,z',u,v,w,uD,vD,wD⟩,
  use (u.append v).append w,
  rw [walk.support_append,list.to_finset_append,walk.support_append,list.to_finset_append],
  rw [finset.coe_union,finset.coe_union],

  have vD' := set.subset.trans (list.to_finset_tail v.support) vD,
  have wD' := set.subset.trans (list.to_finset_tail w.support) wD,
  exact set.union_subset (set.union_subset uD vD') wD',
end

lemma ends_product [Vnempty : nonempty V] [Vnempty' : nonempty V']
  [locally_finite G] [locally_finite G']
  (Gpc :G.preconnected) (Gpc' : G'.preconnected)
  (Vinf : set.infinite (@set.univ V)) (Vinf' : set.infinite (@set.univ V'))
: ends  (box_prod G  G') (simple_graph.preconnected.box_prod Gpc Gpc') ≃ true :=
begin

  let VV := V × V',
  let GG := G □ G',
  let GGpc := simple_graph.preconnected.box_prod Gpc Gpc',
  haveI : locally_finite GG, by sorry,
  haveI all_fin : ∀ K : finset VV, fintype (inf_ro_components GG K),
    from λ K, inf_components_finite' GG GGpc K,
  suffices : ∀ K : finset VV, fintype.card (inf_ro_components GG K) = 1,
  {
    have all_inj : ∀ (K L : finset VV) (KL : K ⊆ L), injective (bwd_map GG GGpc KL), by {
      rintros K L KL,
      refine ((fintype.bijective_iff_surjective_and_card (bwd_map GG GGpc KL)).mpr ⟨_,_⟩).1,
      exact bwd_map_surjective GG GGpc KL,
      exact (this L).trans (this K).symm,
    },
    have that := eval_bijective GG GGpc ∅ (λ L KL, all_inj ∅ L KL),
    refine (equiv.of_bijective _ that).trans (equiv_true_of (inf_ro_components GG ∅) _),
    --
    let lol2 := (fintype.card_eq_one_iff.mp (this ∅)),
    exact lol2,
  },

  rintros K,
  let L := finset.product (finset.image prod.fst K) (finset.image prod.snd K),
  have : K ⊆ L, from subset_product,
  let D := (L : set VV) ᶜ,

  have Ddis : disjoint D K, from disjoint_compl_left_iff.mpr (‹K⊆L›),
  have Dinf : D.infinite, by sorry, -- VV is infinite, L is finite, V\L is infinite.
  have Dconn : subconnected GG D,
    from finprod_compl_subconnected G G' Gpc Gpc' Vinf Vinf' _ _,
  -- If I do a `rcases … with ⟨C,Ccomp⟩` here I get elimination out of prop issues, why does this ↓ work?
  let C := (ro_component.of_subconnected_disjoint GG K D (set.infinite.nonempty Dinf) Ddis Dconn).some,
  obtain ⟨Ccomp,DC⟩ := (ro_component.of_subconnected_disjoint GG K D (set.infinite.nonempty Dinf) Ddis Dconn).some_spec,
  have Cinf := set.infinite.mono DC Dinf,
  suffices : ∀ C' ∈ inf_ro_components GG K, C' = C, {
    apply fintype.card_eq_one_iff.mpr,
    use ⟨C,Ccomp,Cinf⟩,
    rintro ⟨D,Dcomp,Dinf⟩,
    simp,
    exact this D ⟨Dcomp,Dinf⟩,
  },
  rintros C' ⟨Ccomp',Cinf'⟩,
  suffices : (C ∩ C').nonempty, {
    rcases this with ⟨x,xC,xC'⟩,
    apply eq_of_common_mem GG K C' C Ccomp' Ccomp x xC' xC},
  by_contradiction,
  have : C' ⊆ L, by {
    rw set.not_nonempty_iff_eq_empty at h,
    rw ←set.disjoint_iff_inter_eq_empty at h,
    have := @disjoint.mono_left _ _ _ D C C' DC h,
    rw ←set.disjoint_compl_right_iff_subset,
    exact this.symm,
  },
  exact Cinf' (set.finite.subset L.finite_to_set this),
end

end product
-/

end ends

end simple_graph
