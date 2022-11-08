/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import combinatorics.quiver.basic
import combinatorics.quiver.colored
import data.list
import group_theory.group_action.basic

open function

universes u v w

namespace quiver

section defs

variables (V : Type*) {M : Type*} [has_smul M V] {S : Type*} (ι : S → M)

inductive schreier_graph.arrow : V → V → Sort*
| mk (m : S) (x : V) : schreier_graph.arrow (x) (ι m • x)


@[instance] def schreier_graph_colored_quiver : colored_quiver V S :=
{ hom := schreier_graph.arrow V ι,
  color := by {apply schreier_graph.arrow.rec, exact (λ s v, s)} }

def star_bij {x: V} : (Σ y, schreier_graph.arrow V ι x y) ≃ S :=
{ to_fun := by { rintro ⟨s,a⟩, cases a, assumption, },
  inv_fun := by { rintro s, use ι s • x, constructor, },
  left_inv := by { rintro ⟨s,a⟩, cases a, simp, },
  right_inv := by { rintro s, simp, } }

def arrows_bij {x y : V} : (schreier_graph.arrow V ι x y) ≃ {s : S | ι s • x = y} :=
{ to_fun := by {apply schreier_graph.arrow.rec, rintro s x, exact ⟨s,rfl⟩, },
  inv_fun := by { rintro ⟨s,e⟩, cases e, constructor, },
  left_inv := by { apply schreier_graph.arrow.rec, rintro s x, simp, },
  right_inv := by { rintro ⟨s,e⟩, dsimp at e, subst_vars, } }

end defs

namespace schreier_graph

section basic

variables {X : Type*} {M : Type*} [has_smul M X] {S : Type*} (ι : S → M)

lemma mono {S} {T : set M} (h : S ≤ T) : schreier_graph X S ≤ schreier_graph X T :=
begin
  apply simple_graph.from_rel_mono,
  rintros _ _ ⟨⟨m, mS⟩, x⟩,
  exact adj_gen.mk ⟨m, h mS⟩ x,
end

lemma adj_iff {x y : X} : (schreier_graph X S).adj x y ↔ (x ≠ y ∧ ∃ m ∈ S, m • x = y ∨ m • y = x) :=
begin
  simp only [schreier_graph, adj_gen_iff, from_rel_adj, ne.def, set_coe.exists],
  congr', ext, split,
  { rintros (⟨m,h,rfl⟩|⟨m,h,rfl⟩), exact ⟨m,h,or.inl rfl⟩, exact ⟨m,h,or.inr rfl⟩, },
  { rintros ⟨m,h,(rfl|rfl)⟩, exact or.inl ⟨m,h,rfl⟩, exact or.inr ⟨m,h,rfl⟩, },
end

lemma neighbor_set_eq {x : X} :
  (schreier_graph X S).neighbor_set x = {y | x ≠ y ∧ ∃ m ∈ S, m • x = y ∨ m • y = x} :=
by { dsimp [neighbor_set, set_of], ext, rw adj_iff, }

lemma neighbor_set_eq' {x : X} :
  (schreier_graph X S).neighbor_set x
= {y | x ≠ y} ∩ ({y | ∃ m ∈ S, m • x = y} ∪ {y | ∃ m ∈ S, m • y = x}) :=
begin
  simp only [schreier_graph, ne.def, exists_prop], ext,
  simp only [mem_neighbor_set, set.mem_inter_iff, set.mem_set_of_eq, set.mem_union,
             simple_graph.from_rel_adj, adj_gen_iff, ne.def, set_coe.exists, exists_prop,
             and.congr_right_iff],
  rintro, congr'; ext; tauto,
end

end basic

section group_action

variables {X : Type*} {G : Type*} [group G] [mul_action G X] (S : set G)

lemma eq_add_inverses_remove_one :
  (schreier_graph X S) = (schreier_graph X $ (S ∪ (set.image (λ x : G, x ⁻¹) S)) \ {(1 : G)}) :=
begin
  ext x y,
  simp only [adj_iff, ne.def, exists_prop, set.mem_diff, set.mem_union, set.mem_image,
             set.mem_singleton_iff, and.congr_right_iff],
  rintro ne, split,
  { rintro ⟨m,mS,(l|r)⟩,
    { use [m,mS], rintro rfl, simp [one_smul] at l, exact ne l, left, exact l, },
    { use [m,mS], rintro rfl, simp only [one_smul] at r, exact ne r.symm, right, exact r}, },
  { rintros ⟨m,⟨⟨(mS|⟨n,nS,rfl⟩),b⟩,e⟩⟩,
    { use [m,mS,e], },
    { use [n,nS], rw [inv_smul_eq_iff, inv_smul_eq_iff] at e, tauto, }, },
end

lemma reachable_iff {x y : X} :
  (schreier_graph X S).reachable x y ↔ ∃ g ∈ (subgroup.closure S), g • x = y :=
begin
  split,
  { rintro ⟨w⟩,
    induction w,
    { exact ⟨1, subgroup.one_mem _, one_smul _ w⟩, },
    { obtain ⟨g,gS,rfl⟩ := w_ih,
      rw adj_iff at w_h,
      rcases w_h with ⟨ne,⟨m,h,(rfl|rfl)⟩⟩,
      { refine ⟨g*m, _, mul_smul _ _ _⟩,
        exact (subgroup.closure S).mul_mem gS (subgroup.subset_closure h), },
      { refine ⟨g * m ⁻¹, _, _⟩, rotate, simp only [mul_smul, inv_smul_eq_iff, smul_left_cancel_iff],
        exact (subgroup.closure S).mul_mem gS
          ((subgroup.closure S).inv_mem $ subgroup.subset_closure h), }, }, },
  { rintro ⟨g, gS, rfl⟩, revert x,
    apply subgroup.closure_induction gS,
    { rintro g gS x,
      by_cases h' : g • x = x,
      { rw h', },
      { constructor,
        apply adj.to_walk,
        rw adj_iff, refine ⟨ne.symm h', g, gS, or.inl rfl⟩, }, },
    { rintro x, simp, },
    { rintro g₁ g₂ xg₁ xg₂ x,
      rw [mul_smul],
      apply reachable.trans (@xg₂ x) (@xg₁ (g₂ • x)), },
    { rintro g xg x,
      apply reachable.symm,
      convert @xg (g ⁻¹ • x),
      simp only [smul_inv_smul], }, },
end

abbreviation schreier_coset_graph (H : subgroup G) := schreier_graph (G ⧸ H) S

noncomputable def equiv_coset_graph_of_pretransitive [mul_action.is_pretransitive G X] (x₀ : X) :
  schreier_coset_graph S (mul_action.stabilizer G x₀) ≃g schreier_graph X S :=
{ to_equiv     := (mul_action.equiv_quotient_stabilizer G x₀).symm,
  map_rel_iff' := λ x y, by
  { simp only [adj_iff, mul_action.equiv_quotient_stabilizer, equiv.symm_symm,
               equiv.of_bijective_apply, ne.def, exists_prop,
               ←mul_action.of_quotient_stabilizer_smul],
    simp only [injective.eq_iff (mul_action.injective_of_quotient_stabilizer G x₀)], } }

instance [decidable_eq X] [h : fintype S] : locally_finite (schreier_graph X S) :=
begin
  rintro x, rw neighbor_set_eq',
  haveI : fintype ↥{y : X | ∃ (m : G) (H : m ∈ S), m • x = y}, by
  { convert set.fintype_image S (•x),
    simp only [exists_prop], },
  haveI : fintype ↥{y : X | ∃ (m : G) (H : m ∈ S), m • y = x}, by
  { simp_rw [←eq_inv_smul_iff],
    convert set.fintype_image S (λ g, g⁻¹•x),
    simp only [exists_prop],
    ext, congr', ext, tauto, },
  apply_instance,
end

end group_action

abbreviation cayley_graph {G : Type*} [group G] (S : set G) := schreier_graph G S

section cayley_graph

variables {G : Type*} [group G] (S : set G)

def as_automorphism (g : G) : (cayley_graph S ≃g cayley_graph S) :=
{ to_equiv := equiv.mul_right (g⁻¹),
  map_rel_iff' := λ a b, by
  { simp only [adj_iff, equiv.coe_mul_right, ne.def, mul_left_inj, smul_eq_mul, exists_prop,
               and.congr_right_iff],
    simp only [←mul_assoc, injective.eq_iff (group.mul_right_bijective (g⁻¹)).left],
    exact λ _, iff.rfl, } }

lemma as_automorphism_apply (g x : G) : (as_automorphism S g) x = x * g⁻¹ := rfl

def as_automorphism_group : G →* (cayley_graph S ≃g cayley_graph S) :=
{ to_fun := as_automorphism S,
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
