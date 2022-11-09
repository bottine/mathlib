/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import combinatorics.quiver.basic
import data.list
import algebra.group.defs
import group_theory.group_action.basic
import group_theory.group_action.group
import group_theory.group_action.defs
import group_theory.subgroup.basic
import group_theory.coset
import group_theory.quotient_group
import group_theory.group_action.quotient



open function

universes u v w

namespace quiver

instance iso_group {V : Type*} [quiver.{u+1} V] : group (V ≃q V) := sorry

section coloring

class coloring (V S : Type*) [quiver V] :=
(color : ∀ {u v : V}, (u ⟶ v) → S)

def color {V : Type*} (S : Type*) [quiver V] [coloring V S] {X Y : V} (f : X ⟶ Y) : S :=
coloring.color f

end coloring

section defs

inductive schreier_graph.arrow (V : Type*) {M S : Type*} [has_smul M V] (ι : S → M) : V → V → Sort*
| mk (m : S) (x : V) : schreier_graph.arrow (x) (ι m • x)

def schreier_graph (V : Type*) {M S : Type*} [has_smul M V] (ι : S → M) := V

instance (V : Type*) {M S : Type*} [h : has_smul M V] (ι : S → M) :
  has_smul M (schreier_graph V ι) := h

abbreviation sg := schreier_graph

variables (V : Type*) {M S : Type*} [has_smul M V] (ι : S → M)

def to_schreier_graph : V → sg V ι := id
def of_schreier_graph : sg V ι → V := id

@[simp]
lemma schreier_graph_eq : sg V ι = V := rfl


instance schreier_graph_quiver : quiver (sg V ι) := ⟨schreier_graph.arrow V ι⟩
instance schreier_graph_coloring : quiver.coloring (sg V ι) S :=
⟨λ x y a, a.rec_on $ by { rintro s v, exact s, }⟩

def schreier_graph.star_bij {x : sg V ι} : (Σ y, schreier_graph.arrow V ι x y) ≃ S :=
{ to_fun := by { rintro ⟨s,a⟩, cases a, assumption, },
  inv_fun := by { rintro s, use ι s • x, constructor, },
  left_inv := by { rintro ⟨s,a⟩, cases a, simp, },
  right_inv := by { rintro s, simp, } }

def schreier_graph.arrows_bij {x y : sg V ι} :
  (schreier_graph.arrow V ι x y) ≃ {s : S | ι s • x = y} :=
{ to_fun := by {apply schreier_graph.arrow.rec, rintro s x, exact ⟨s,rfl⟩, },
  inv_fun := by { rintro ⟨s,e⟩, cases e, constructor, },
  left_inv := by { apply schreier_graph.arrow.rec, rintro s x, simp, },
  right_inv := by { rintro ⟨s,e⟩, dsimp at e, subst_vars, } }

end defs

section group_action

variables {V : Type*} {G S : Type*} [group G] [mul_action G V] (ι : S → G)

abbreviation schreier_coset_graph (H : subgroup G) := schreier_graph (G ⧸ H) ι

/-
noncomputable def equiv_coset_graph_obj [mul_action.is_pretransitive G V] (x₀ : V) :
  schreier_coset_graph ι (mul_action.stabilizer G x₀) → schreier_graph V ι :=
(mul_action.equiv_quotient_stabilizer G x₀).symm.to_fun

noncomputable def equiv_coset_graph_map [mul_action.is_pretransitive G V] (x₀ : V)
  (X Y : schreier_coset_graph ι (mul_action.stabilizer G x₀)) (f : X ⟶ Y) :
  (equiv_coset_graph_obj ι x₀ X ⟶ equiv_coset_graph_obj ι x₀ Y) :=
begin
  revert f X Y,
  apply schreier_graph.arrow.rec,
  rintro m x,
  fapply quot.hrec_on x,
  rintro g,
  dsimp [equiv_coset_graph_obj, mul_action.equiv_quotient_stabilizer,
         mul_action.of_quotient_stabilizer, quotient.lift_on', quotient.lift_on,quot.lift_on,
         has_smul.smul, quotient.map', quot.map],
  rw [mul_smul (ι m) g x₀], constructor,
  rintro g h gh, simp,
  have : g • x₀ = h • x₀, by
  { symmetry,
    rw [←inv_smul_eq_iff, ←mul_smul, ←mul_action.mem_stabilizer_iff,
        ←quotient_group.left_rel_apply], exact gh, },


end

noncomputable def equiv_coset_graph [mul_action.is_pretransitive G V] (x₀ : V) :
  schreier_coset_graph ι (mul_action.stabilizer G x₀) ≃q schreier_graph V ι :=
{ obj := equiv_coset_graph_obj ι x₀,
  bij_obj := by { apply equiv.bijective, },
  map := sorry,
  bij_map := sorry }

lemma equiv_coset_graph.color [mul_action.is_pretransitive G V] (x₀ : V)
  {X Y : schreier_coset_graph ι (mul_action.stabilizer G x₀)} (f : X ⟶ Y) :
  color S ((equiv_coset_graph ι x₀).map f) = color S f := sorry
-/

end group_action

abbreviation cayley_graph {G : Type*} [group G] {S : Type*} (ι : S → G) := schreier_graph G ι

section cayley_graph

variables {G : Type*} [group G] {S : Type*} (ι : S → G)

def as_automorphism (g : G) : cayley_graph ι ≃q cayley_graph ι :=
{ obj := equiv.mul_right (g⁻¹),
  bij_obj := sorry,
  map := sorry,
  bij_map := sorry }

lemma as_automorphism_obj_apply (g x : G) : (as_automorphism ι g).obj x = x * g⁻¹ := rfl

def as_automorphism_group : G →* (cayley_graph ι ≃q cayley_graph ι) :=
{ to_fun := as_automorphism ι,
  map_one' := by { dsimp [as_automorphism], ext, simp, },
  map_mul' := λ g g', by { dsimp [as_automorphism], ext, simp, } }

lemma injective_as_automorphism_group : function.injective (as_automorphism_group S) :=
begin
  rintro g g' h,
  simp only [as_automorphism_group, as_automorphism, equiv.mul_right, to_units, units.mul_right,
             inv_inv, units.inv_mk, units.coe_mk, mul_equiv.coe_mk, monoid_hom.coe_mk] at h,
  simpa using congr_fun h.left 1,
end

def translate_walk {g h k : G} (w : (cayley_graph S).walk g h) :
  (cayley_graph S).walk (g * k) (h * k) :=
begin
  induction w,
  { exact walk.nil, },
  { apply walk.cons _ (w_ih),
    rw [←inv_inv k, ←as_automorphism_apply S k⁻¹ w_u, ←as_automorphism_apply S k⁻¹ w_v,
        simple_graph.iso.map_adj_iff],
    exact w_h, },
end

lemma connected_iff : (cayley_graph S).connected ↔ subgroup.closure S = ⊤ :=
begin
  rw connected_iff,
  simp only [(⟨1⟩ : nonempty G), and_true],
  split,
  { rw eq_top_iff, rintro h x _,
    obtain ⟨g,gS,rfl⟩ := (reachable_iff S).mp (h (1 : G) x),
    simpa only [smul_eq_mul, mul_one] using gS, },
  { rintro h g g',
    simp only [reachable_iff, h, subgroup.mem_top, smul_eq_mul, exists_true_left],
    refine ⟨g' * g⁻¹, _⟩, simp only [inv_mul_cancel_right], },
end

end cayley_graph

end schreier_graph

end quiver
