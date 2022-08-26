import category_theory.filtered
import topology.category.Top.limits
import data.finset.basic

import .conn_comp_outside
import .mathlib_fintype_inverse_systems

open category_theory
open opposite
open simple_graph
open classical
open simple_graph.conn_comp_outside

/- Implementing Kyle Miller's suggestion:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Geometric.20group.20theory/near/290624806 -/

noncomputable theory
local attribute [instance] prop_decidable

universes u v w
variables {V : Type u} [decidable_eq V] (h : V ≃ ℕ)
variables (G : simple_graph V) [locally_finite G]


-- Defined backwards for simpler use of `mathlib_fintype_inverse_systems.lean`
instance finset_preorder : preorder (finset V) := {
  le := λ A B, A ⊇ B,
  lt := λ A B, A ⊃ B,
  le_refl := by obviously,
  le_trans := by obviously,
  lt_iff_le_not_le := by {dsimp only [superset,ssuperset],obviously,}
  }

/- The category of finite subsets of `V` with the morphisms being inclusions -/
instance FinIncl : category (finset V) := infer_instance

instance finset_directed : is_directed (finset V) (≥) := {
  directed := λ A B, ⟨A ∪ B, ⟨finset.subset_union_left A B, finset.subset_union_right A B⟩⟩ }

/-The functor assigning a finite set in `V` to the set of connected components in its complement-/
def ComplComp : finset V ⥤ Type u := {
  obj := λ A, conn_comp_outside G A,
  map := λ _ _ f, conn_comp_outside_back (le_of_hom f),
  map_id' := by {intro, funext, simp, apply conn_comp_outside_back.refl,},
  map_comp' := by {intros, funext, simp, symmetry, apply conn_comp_outside_back.trans,},
}

def Ends := (ComplComp G).sections

/-/-The functor assigning a finite set in `V` to the set of **infinite** connected components in its complement-/
def ComplInfComp : finset V ⥤ Type u := {
  obj := λ A, inf_conn_comp_outside G A,
  map := λ _ _ f, inf_conn_comp_outside_back (le_of_hom f),
  map_id' := by {intro, funext, simp, apply subtype.eq, rw [inf_conn_comp_outside_back.def], apply conn_comp_outside_back.refl, },
  map_comp' := by {intros, funext, simp, symmetry, apply subtype.eq, repeat {rw [inf_conn_comp_outside_back.def]}, apply conn_comp_outside_back.trans, },
}-/


def ComplInfComp : finset V ⥤ Type u :=
  (ComplComp G).subfunctor
    (λ K, {C : conn_comp_outside G K | C.verts.infinite})
    (by {intros _ _ _, apply conn_comp_outside_back.inf_to_inf,})

def Endsinfty := (ComplInfComp G).sections

lemma ComplInfComp.obj : ∀ K : finset V, (ComplInfComp G).obj K = inf_conn_comp_outside G K := by {intro, refl,}

lemma ComplInfComp.map : ∀ {K L : finset V}, ∀ f : K ⟶ L, (ComplInfComp G).map f = inf_conn_comp_outside_back (le_of_hom f) := by {intros, ext ⟨_, _⟩, refl,}


lemma ComplInfComp_eq_ComplComp_to_surjective : ComplInfComp G = inverse_system.to_surjective (ComplComp G) :=
begin
  apply functor.subfunctor.ext,
  dsimp [ComplComp], intro K, ext C,
  show C.verts.infinite ↔ C ∈ (⋂ (i : {L // K ⊆ L}), _),
  rw [inf_conn_comp_outside.iff_in_all_range],
  obviously,
end

lemma Ends_equiv_Endsinfty : Ends G ≃ Endsinfty G :=
begin
  dsimp [Ends,Endsinfty],
  rw ComplInfComp_eq_ComplComp_to_surjective,
  apply inverse_system.to_surjective.sections_equiv,
end


instance ComplComp_nonempty [infinite V] :  ∀ (j : (finset V)), nonempty ((ComplComp G).obj j) := by {
  intro K, dsimp [ComplComp],
  refine nonempty.map subtype.val _,
  rotate, apply inf_graph_has_inf_conn_comp,}

instance ComplComp_fintype [Gpc : preconnected G] : Π (j : (finset V)), fintype ((ComplComp G).obj j) := by
{ intro, exact finite_components _ _ Gpc,}

instance ComplInfComp_nonempty [infinite V] :
  Π (j : (finset V)), nonempty ((ComplInfComp G).obj j) := by
{ intro, apply inf_graph_has_inf_conn_comp,}

instance ComplInfComp_fintype [Gpc : preconnected G] : Π (j : (finset V)), fintype ((ComplInfComp G).obj j) := by
{ intro K, dsimp [ComplInfComp],
  haveI := (finite_components _ K Gpc),
  apply subtype.fintype,}



lemma all_empty [finite V] : ∀ (K : finset V), is_empty ((ComplInfComp G).obj K) :=
begin
  sorry,
end

lemma ComplInfComp.surjective : inverse_system.is_surjective (ComplInfComp G) :=
begin
  dsimp [Endsinfty],
  rw ComplInfComp_eq_ComplComp_to_surjective,
  by_cases hfin : finite V,
  { haveI := hfin,
    rintro i j h x,
    let jempty := all_empty  G j,
    rw ComplInfComp_eq_ComplComp_to_surjective at jempty,
    exact jempty.elim x, },
  { haveI : infinite V := infinite.of_not_finite hfin,
    exact @inverse_system.to_surjective.is_surjective _ _ _ (ComplComp G) _ (ComplComp_nonempty G), },
end

lemma Endsinfty_surjective : Π (j : (finset V)), function.surjective (λ e : Endsinfty G, e.val j) :=
begin
  rintro j,
  dsimp [Endsinfty],
  have := ComplInfComp.surjective G,
  rw inverse_system.is_surjective_iff at this,
  apply inverse_system.sections_surjective,
  rintro i h, exact this i j h,
end

lemma Endsinfty_eventually_constant [Gpc : preconnected G]
  (K : finset V)
  (top : Π (L : finset V) (KL : L ≤ K), (ComplInfComp G).obj L ≃ (ComplInfComp G).obj K) :
  Endsinfty G ≃ (ComplInfComp G).obj K :=
begin

  by_cases hfin : finite V, rotate,
  { haveI : infinite V := infinite.of_not_finite hfin,
    haveI :  Π (j : (finset V)), nonempty ((ComplComp G).obj j), from ComplComp_nonempty G,
    apply equiv.of_bijective _ (inverse_system.sections_bijective (ComplInfComp G) K _),
    rintros ⟨L,KL⟩,
    have sur : function.surjective ((ComplInfComp G).map (hom_of_le KL)), by {
      rw (ComplInfComp_eq_ComplComp_to_surjective G),
      rintros a,
      exact (inverse_system.to_surjective.is_surjective (ComplComp G) L K KL a),
    },
    split, rotate,
    { exact sur },
    { exact (fintype.injective_iff_surjective_of_equiv (top L KL)).mpr sur },},
  { -- degenerate case: If V is finite, then everything is empty,
    haveI := hfin,
    have :  Π (j : (finset V)), is_empty ((ComplInfComp G Gpc).obj j), from all_empty G Gpc,
    apply equiv.of_bijective,
    apply inverse_system.sections_bijective (ComplInfComp G Gpc),
    rintro ⟨L,KL⟩,
    -- Have to show that a map A → B with both A and B empty is necessarily a bijection.
    unfold function.bijective, split,
    { rintro x, exact (this L).elim x,},
    { rintro y, exact (this K).elim y,},}
end