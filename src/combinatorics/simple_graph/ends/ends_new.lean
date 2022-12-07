/-
Copyright (c) 2022 Anand Rao, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao, Rémi Bottinelli
-/
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import data.set_like.basic
import category_theory.category.basic
import category_theory.filtered
import topology.category.Top.limits

universes u

variables {V : Type u} (G : simple_graph V) (K L L' M : set V)

open classical

noncomputable theory
local attribute [instance] prop_decidable

namespace simple_graph

section out

/-- The graph induced by removing `K` -/
abbreviation out := (G.induce $ K ᶜ)

/-- Subsetship induces an obvious map on the induced graphs. -/
abbreviation out_hom {K L} (h : K ⊆ L) : G.out L →g G.out K :=
{ to_fun := λ v, ⟨v.val, set.compl_subset_compl.mpr h v.prop⟩,
  map_rel' := λ v w, by { cases v, cases w, simp, } }

lemma out_hom_refl (K) : G.out_hom (subset_refl K) = hom.id :=
by { ext, simp only [subtype.val_eq_coe, rel_hom.coe_fn_mk, subtype.coe_eta, rel_hom.id_apply], }

lemma out_hom_trans {K L M} (h : K ⊆ L) (h' : L ⊆ M) :
  G.out_hom (h.trans h') = (G.out_hom h).comp (G.out_hom h') :=
by { ext, simp only [rel_hom.coe_fn_mk, hom.coe_comp], }

lemma out_hom_injective {K} {L} (h : K ⊆ L) : function.injective (G.out_hom h) := λ v v' e,
by { simpa only [subtype.val_eq_coe, rel_hom.coe_fn_mk, subtype.mk_eq_mk,
                 subtype.ext_iff] using e, }

end out

/-- The components outside a given set of vertices `K` -/
abbreviation comp_out := (G.out K).connected_component

variables {G} {K L M}

@[reducible, simp] def comp_out.supp (C : G.comp_out K) : set V :=
  { v : V | ∃ (h : v ∈ K ᶜ), connected_component_mk (G.out K) ⟨v,h⟩ = C }

@[ext] lemma comp_out.eq_of_eq_supp (C D : G.comp_out K) : C = D ↔ C.supp = D.supp :=
begin
  split,
  { rintro ⟨⟩, refl, },
  { refine connected_component.ind₂ _ C D,
    rintros ⟨v,hv⟩ ⟨w,hw⟩ h,
    simp_rw [set.ext_iff] at h,
    replace h := (h v).mp,
    simp only [set.mem_compl_iff, connected_component.eq, set.mem_set_of_eq,
              forall_exists_index] at h,
    simp only [connected_component.eq],
    exact (h hv (reachable.refl _)).some_spec, }
end

instance : set_like (G.comp_out K) V :=
{ coe := comp_out.supp,
  coe_injective' := by {intros C D, apply (comp_out.eq_of_eq_supp _ _).mpr, } }

abbreviation comp_out_of_vertex (G : simple_graph V) {v : V} (vK : v ∈ K ᶜ) : G.comp_out K :=
  connected_component_mk (G.out K) ⟨v,vK⟩

lemma comp_out_of_vertex_mem (G : simple_graph V) {v : V} (vK : v ∈ K ᶜ) :
  v ∈ (G.comp_out_of_vertex vK : G.comp_out K) := sorry

namespace comp_out

@[simp] lemma mem_supp_iff {v : V} {C : comp_out G K} :
  v ∈ C ↔ ∃ (vK : v ∈ K ᶜ), connected_component_mk (G.out K) ⟨v,vK⟩ = C := by refl

@[reducible,protected]
def subgraph (C : comp_out G K) : G.subgraph := (⊤ : G.subgraph).induce (C : set V)

/-- Infinite connected components -/
@[reducible]
def inf (C : G.comp_out K) := (C : set V).infinite

/-- Finite connected components -/
@[reducible,protected]
def fin (C : G.comp_out K) := (C : set V).finite

lemma eq_of_eq_set {C D : G.comp_out K} : (C : set V) = (D : set V) ↔ C = D := by simp

@[simp] lemma nempty (C : G.comp_out K) : (C : set V).nonempty := by
{ refine C.ind _,
  rintro v,
  use v,
  simp only [set.mem_compl_iff, set_like.mem_coe, mem_supp_iff, connected_component.eq,
             subtype.coe_eta, exists_prop],
  exact ⟨v.prop, reachable.refl _⟩, }

@[protected]
lemma outside (C : G.comp_out K) : disjoint K C :=
begin
  rw set.disjoint_iff,
  rintro v ⟨vK,vC⟩,
  simp only [mem_supp_iff, set.mem_compl_iff, set_like.mem_coe] at vC,
  exact vC.some vK,
end

lemma not_mem_of_mem {C : G.comp_out K} {c : V} (cC : c ∈ C) : c ∉ K :=
λ cK, set.disjoint_iff.mp C.outside ⟨cK,cC⟩

@[protected]
lemma disjoint (C D : G.comp_out K) (ne : C ≠ D) : disjoint (C : set V) (D : set V) :=
begin
  revert C D,
  refine connected_component.ind₂ _,
  rintro ⟨v,vK⟩ ⟨w,wK⟩ ne,
  rw set.disjoint_iff,
  rintro u ⟨uv, uw⟩,
  apply ne, clear ne,
  simp only [connected_component.eq, set.mem_compl_iff, set_like.mem_coe, mem_supp_iff] at uv uw ⊢,
  exact uv.some_spec.symm.trans uw.some_spec,
end

lemma eq_of_not_disjoint (C D : G.comp_out K) (nd : ¬ disjoint (C : set V) (D : set V)) : C = D :=
begin
  rw set.not_disjoint_iff at nd,
  simp only [set_like.mem_coe, mem_supp_iff] at nd,
  obtain ⟨x,⟨_,rfl⟩,⟨_,rfl⟩⟩ := nd, refl,
end

lemma nonadj (C : G.comp_out K) : ¬ (∃ (c d : V), c ∈ C ∧ d ∉ C ∧ d ∉ K ∧ G.adj c d) :=
begin
  revert C,
  refine connected_component.ind _,
  rintro v,
  rintro ⟨c,d,cC,dnC,dnK,cd⟩,
  have cd' : (G.out K).reachable (⟨c,not_mem_of_mem cC⟩) ⟨d,dnK⟩ :=
    adj.reachable (by simpa using cd),
  simp only [set.mem_compl_iff, mem_supp_iff, connected_component.eq, not_exists] at cC dnC,
  exact dnC dnK (cC.some_spec.symm.trans cd').symm,
end

lemma adj [Gc : G.preconnected] [hK : K.nonempty] :
  ∀ (C : G.comp_out K), ∃ (ck : V × V), ck.1 ∈ C ∧ ck.2 ∈ K ∧ G.adj ck.1 ck.2 :=
begin
  refine connected_component.ind (λ v, _),
  let C : G.comp_out K := G.comp_out_of_vertex v.prop,
  let dis := set.disjoint_iff.mp C.outside,
  by_contra' h,
  suffices : set.univ = (C : set V),
  { exact dis ⟨hK.some_spec, this ▸ (set.mem_univ hK.some)⟩, },
  symmetry,
  rw set.eq_univ_iff_forall,
  rintro u,
  by_contradiction unC,
  obtain ⟨p⟩ := Gc v u,
  obtain ⟨x,y,xy,xC,ynC⟩ :=
    p.disagreeing_adj_pair (C : set V) (G.comp_out_of_vertex_mem v.prop) unC,
  refine @nonadj V G K C _,
  have : (G.out K).connected_component_mk v = G.comp_out_of_vertex v.prop, by simp,
  rw this at h,
  exact ⟨x,y,xC,ynC,λ (yK : y ∈ K), h ⟨x,y⟩ xC yK xy, xy⟩,
end

lemma connected (C : G.comp_out K) : C.subgraph.connected := sorry

-- The unique connected component containing a connected set disjoint from `K`
def of_connected_disjoint (S : set V)
  (conn : ((⊤ : G.subgraph).induce S).connected) (dis : disjoint K S) : G.comp_out K :=
begin
  cases conn with pre nem,
  obtain ⟨v,vS⟩ := nem.some,
  rw set.disjoint_iff at dis,
  exact G.comp_out_of_vertex (λ (h : v ∈ K), dis ⟨h,vS⟩),
end

lemma of_connected_disjoint_sub (S : set V)
  (conn : ((⊤ : G.subgraph).induce S).connected) (dis : disjoint K S) :
  S ⊆ (of_connected_disjoint S conn dis : set V) :=
begin
  have : ∀ s t : S, (G.induce S).adj s t → (G.out K).adj s t, by
  { rintro ⟨s,sS⟩ ⟨t,tS⟩ a,
    simp only [subtype.coe_mk, comap_adj, embedding.coe_subtype,out] at a ⊢,
    exact ⟨(λ sK, (set.disjoint_iff).mp dis ⟨sK,sS⟩),(λ tK, (set.disjoint_iff).mp dis ⟨tK,tS⟩),a⟩,},
  have : ∀ s t : S, (G.induce S).reachable s t → (G.out K).reachable s t, by {
    rintro ⟨s,hs⟩ ⟨t,ht⟩ ⟨r⟩,
    constructor,
    induction r,
    { exact nil, },
    { apply walk.cons (this r_u r_v r_h) r_ih,},},
  rw connected_iff at conn,
  rintro s sS,
  dsimp only [of_connected_disjoint,of_vertex],
  simp only [set_like.mem_coe, mem_supp_iff, connected_component.eq],
  exact this ⟨s,sS⟩ conn.right.some (conn.left ⟨s,sS⟩ conn.right.some),
end

/-
abbreviation hom (C : G.comp_out L) (h : K ⊆ L) : G.comp_out K := C.map (G.out_hom h)

lemma hom_eq_iff_le (C : G.comp_out L) (h : K ⊆ L) (D : G.comp_out K) :
  C.hom h = D ↔ (C : set V) ⊆ (D : set V) :=
begin
  sorry
end

lemma hom_refl (C : G.comp_out L) : C.hom (subset_refl L) = C :=
by { change C.map _ = C, rw [G.out_hom_refl L, C.map_id], }


lemma hom_trans (C : G.comp_out L) (h : K ⊆ L) (h' : M ⊆ K) :
  C.hom (h'.trans h) = (C.hom h).hom h' :=
by { change C.map _ = (C.map _).map _, rw [G.out_hom_trans, C.map_comp], }

end comp_out

section ends

variables (G)

open category_theory

-- Defined homwards for simpler use of `mathlib_fintype_inverse_systems.lean`
instance finset_preorder_reverse : preorder (finset V) :=
{ le := (⊇),
  lt := (⊃),
  le_refl := by obviously,
  le_trans := by obviously,
  lt_iff_le_not_le := by { dsimp only [superset,ssuperset], obviously, } }

/-- The category of finite subsets of `V` with the morphisms being inclusions -/
--instance finset_category : category (finset V) := infer_instance

instance finset_directed : is_directed (finset V) (≥) := {
  directed := λ A B, ⟨A ∪ B, ⟨finset.subset_union_left A B, finset.subset_union_right A B⟩⟩ }

/-- The functor assigning a finite set in `V` to the set of connected components in its complement-/
def comp_out_functor : finset V ⥤ Type u :=
{ obj := λ K, G.comp_out K,
  map := λ _ _ f C, C.hom (le_of_hom f),
  map_id' := λ K, funext $ λ C, C.hom_refl,
  map_comp' := λ K L M h h', funext $ λ C, C.hom_trans (le_of_hom h) (le_of_hom h') }

/-- The end of a graph, defined as the sections of the functor. -/
@[protected]
def «end» := (comp_out_functor G).sections

end ends
-/
end simple_graph
