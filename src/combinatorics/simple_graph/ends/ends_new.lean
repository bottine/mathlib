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

/-- The graph induced by removing `K` -/
abbreviation out := (G.induce $ K ᶜ)

def out_hom {K L} (h : K ⊆ L) : G.out L →g G.out K :=
{ to_fun := λ v, ⟨v.val, set.compl_subset_compl.mpr h v.prop⟩,
  map_rel' := λ v w, by { cases v, cases w, simp, } }

lemma out_hom_id {K} : G.out_hom (subset_refl K) = hom.id := sorry

lemma out_hom_trans {K L M} (h : K ⊆ L) (h' : L ⊆ M) :
  G.out_hom (h.trans h') = (G.out_hom h).comp (G.out_hom h') := sorry

lemma out_hom.injective {K} {L} (h : K ⊆ L) : function.injective (G.out_hom h) :=
by { rintro v v' e, simp [out_hom] at e, exact subtype.ext e, }

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

namespace comp_out

section back

abbreviation back (C : G.comp_out L) (h : K ⊆ L) : G.comp_out K := C.map (G.out_hom h)

lemma back_eq_iff_le (C : G.comp_out L) (h : K ⊆ L) (D : G.comp_out K) :
  C.back h = D ↔ (C : set V) ⊆ (D : set V) :=
begin
  sorry
end

lemma back_refl (C : G.comp_out L) : C.back (le_refl L) = C := sorry
-- use `out_hom_refl`

lemma back_trans (C : G.comp_out L) (h : K ⊆ L) (h' : M ⊆ K) :
  C.back (h'.trans h) = (C.back h).back h' := sorry
-- use `out_hom_trans`


end back

end comp_out

section ends

variables (G)

open category_theory

-- Defined backwards for simpler use of `mathlib_fintype_inverse_systems.lean`
instance finset_preorder_reverse : preorder (finset V) :=
{ le := λ A B, A ⊇ B,
  lt := λ A B, A ⊃ B,
  le_refl := by obviously,
  le_trans := by obviously,
  lt_iff_le_not_le := by { dsimp only [superset,ssuperset], obviously, } }

/-- The category of finite subsets of `V` with the morphisms being inclusions -/
instance finset_category : category (finset V) := infer_instance

instance finset_directed : is_directed (finset V) (≥) := {
  directed := λ A B, ⟨A ∪ B, ⟨finset.subset_union_left A B, finset.subset_union_right A B⟩⟩ }

/-- The functor assigning a finite set in `V` to the set of connected components in its complement-/
def comp_out_functor : finset V ⥤ Type u :=
{ obj := λ K, G.comp_out K,
  map := λ _ _ f C, C.back (le_of_hom f),
  map_id' := λ K, funext $ λ C, C.back_refl,
  map_comp' := λ K L M h h', funext $ λ C, C.back_trans (le_of_hom h) (le_of_hom h') }

/-- The end of a graph, defined as the sections of the functor. -/
@[protected]
def «end» := (comp_out_functor G).sections

end ends

end simple_graph
