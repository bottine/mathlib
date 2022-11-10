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
  simp [prefunctor.is_covering],
  exact  ⟨λ u, function.bijective.comp (hψ.left _) (hφ.left u),
          λ u, function.bijective.comp (hψ.right _) (hφ.right u)⟩,
end
lemma comp' (hψ : ψ.is_covering) (hφψ : (φ ≫q ψ).is_covering ) : φ.is_covering :=
begin
  simp [prefunctor.is_covering],
  split,
  { rintro u,
    rw ←@function.bijective.of_comp_iff' _ _ _ (ψ.star $ φ.obj u) (hψ.left $ φ.obj u) (φ.star u),
    exact hφψ.left u},
  { rintro u,
    rw ←@function.bijective.of_comp_iff' _ _ _ (ψ.costar $ φ.obj u) (hψ.right $ φ.obj u) (φ.costar u),
    exact hφψ.right u},
end
lemma comp'' (hφ : φ.is_covering) (hφψ : (φ ≫q ψ).is_covering) (φsur : function.surjective φ.obj) :
  ψ.is_covering :=
begin
  simp [prefunctor.is_covering],
  split,
  { rintro v,
    obtain ⟨u,rfl⟩ := φsur v,
    rw ←@function.bijective.of_comp_iff _ _ _ (ψ.star $ φ.obj u) (φ.star u)  (hφ.left u),
    exact hφψ.left u, },
  { rintro v,
    obtain ⟨u,rfl⟩ := φsur v,
    rw ←@function.bijective.of_comp_iff _ _ _ (ψ.costar $ φ.obj u) (φ.costar u)  (hφ.right u),
    exact hφψ.right u, },
end

def prefunctor.symmetrify : (symmetrify U) ⟶q (symmetrify V) :=
{ obj := φ.obj,
  map := λ X Y f, sum.cases_on f (λ f, sum.inl (φ.map f)) ((λ g, sum.inr (φ.map g))) }

lemma is_covering.symmetrify (hφ : φ.is_covering) : φ.symmetrify.is_covering :=
begin
  sorry,
end

@[reducible] def path_from (u : U) := Σ v : U, path u v

def prefunctor.path_from (u : U) : path_from u → path_from (φ.obj u) := sorry

lemma prefunctor.path_from_bijective (hφ : φ.is_covering) (u : U) :
  function.bijective (φ.path_from u) := sorry

end quiver
