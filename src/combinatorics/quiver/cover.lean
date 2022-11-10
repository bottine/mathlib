/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import combinatorics.quiver.basic
import combinatorics.quiver.iso
import algebra.group.defs
import group_theory.group_action.basic
import group_theory.group_action.group
import group_theory.group_action.defs
import group_theory.subgroup.basic
import group_theory.coset
import group_theory.quotient_group
import group_theory.group_action.quotient
import combinatorics.quiver.connected_component



open function

universes u v w

namespace quiver

variables {U : Type*} [quiver.{u+1} U]
          {V : Type*} [quiver.{v+1} V] (φ : U ⟶q V)
          {W : Type*} [quiver.{w+1} W] (ψ : V ⟶q W)

@[reducible] def star (u : U) := Σ (v : U), (u ⟶ v)
@[reducible] def costar (u : U) := Σ (v : U), (v ⟶ u)

def prefunctor.star (u : U) : star u → star (φ.obj u) := λ F, ⟨(φ.obj F.1), φ.map F.2⟩
def prefunctor.costar (u : U) : costar u → costar (φ.obj u) := λ F, ⟨(φ.obj F.1), φ.map F.2⟩

@[simp] lemma prefunctor.star_comp (u : U) :
  (φ ≫q ψ).star u = (ψ.star (φ.obj u)) ∘ ((φ.star) u) := rfl
@[simp] lemma prefunctor.costar_comp (u : U) :
  (φ ≫q ψ).costar u = (ψ.costar (φ.obj u)) ∘ ((φ.costar) u) := rfl

@[reducible]
def prefunctor.is_covering :=
  (∀ u, function.bijective (φ.star u)) ∧ (∀ u, function.bijective (φ.costar u))

lemma comp (hφ : φ.is_covering) (hψ : ψ.is_covering) :
  (φ ≫q ψ).is_covering :=
begin
  cases hφ, cases hψ,
  simp only [prefunctor.is_covering, prefunctor.star_comp],
  split; rintro u;
  apply function.bijective.comp, -- (hφ.left $ φ.obj v) (hφ v),
end
lemma comp' (hψ : ψ.is_covering) (φψc : (φ ≫q ψ).is_covering ) : φ.is_covering :=
begin
  simp only [functor.is_covering,functor.star_map_comp],
  rintro v,
  rw ←@function.bijective.of_comp_iff' _ _ _ (φ'.star_map $ φ.obj v) (φ'c $ φ.obj v) (φ.star_map v),
  exact φφ'c v,
end
lemma comp'' (hφ : φ.is_covering) (φψc : (φ ≫q ψ).is_covering) (φsur : function.surjective φ.obj) :
  ψ.is_covering :=
begin
  simp only [functor.is_covering,functor.star_map_comp],
  rintro v,
  obtain ⟨u,rfl⟩ := φsur v,
  rw ←@function.bijective.of_comp_iff _ _ _ (φ'.star_map $ φ.obj u) (φ.star_map u)  (φc u),
  exact φφ'c u,
end

def prefunctor.symmetrify : (symmetrify U) ⟶q (symmetrify V) :=
{ obj := φ.obj,
  map := λ X Y f, sum.cases_on f (λ f, sum.inl (φ.map f)) ((λ g, sum.inr (φ.map g))) }

lemma is_covering.symmetrify (hφ : φ.is_covering) : φ.symmetrify.is_covering := sorry


end quiver
