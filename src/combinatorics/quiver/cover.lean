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

@[simp] lemma prefunctor.star_apply {u v : U} (e : u ⟶ v) :
  φ.star u ⟨v, e⟩ = ⟨φ.obj v, φ.map e⟩ := rfl
@[simp] lemma prefunctor.costar_apply {u v : U} (e : v ⟶ u) :
  φ.costar u ⟨v, e⟩ = ⟨φ.obj v, φ.map e⟩ := rfl

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
  split;
  rintro u,
  { rw ←@function.bijective.of_comp_iff' _ _ _ (ψ.star $ φ.obj u) (hψ.left $ φ.obj u) (φ.star u),
    exact hφψ.left u},
  { rw ←@function.bijective.of_comp_iff' _ _ _ (ψ.costar $ φ.obj u) (hψ.right $ φ.obj u) (φ.costar u),
    exact hφψ.right u},
end
lemma comp'' (hφ : φ.is_covering) (hφψ : (φ ≫q ψ).is_covering) (φsur : function.surjective φ.obj) :
  ψ.is_covering :=
begin
  split;
  rintro v;
  obtain ⟨u,rfl⟩ := φsur v,
  { rw ←@function.bijective.of_comp_iff _ _ _ (ψ.star $ φ.obj u) (φ.star u)  (hφ.left u),
    exact hφψ.left u, },
  { rw ←@function.bijective.of_comp_iff _ _ _ (ψ.costar $ φ.obj u) (φ.costar u)  (hφ.right u),
    exact hφψ.right u, },
end

@[simps]
def prefunctor.symmetrify : (symmetrify U) ⟶q (symmetrify V) :=
{ obj := φ.obj,
  map := λ X Y, sum.map φ.map φ.map }

def symmetrify_star (u : U) : star (symmetrify.of.obj u) ≃ star u ⊕ costar u :=
begin
  fsplit,
  { rintro ⟨v,(f|g)⟩, exact sum.inl ⟨v,f⟩, exact sum.inr ⟨v,g⟩, },
  { rintro (⟨v,f⟩|⟨v,g⟩), exact ⟨v,quiver.hom.to_pos f⟩, exact ⟨v,quiver.hom.to_neg g⟩, },
  { rintro ⟨v,(f|g)⟩, simp, },
  { rintro (⟨v,f⟩|⟨v,g⟩), simp, },
end

@[simp] lemma symmetrify_star_lapply {u v : U} (e : u ⟶ v) :
  symmetrify_star u ⟨v, sum.inl e⟩ = sum.inl ⟨v, e⟩ := rfl
@[simp] lemma symmetrify_star_rapply {u v : U} (e : v ⟶ u) :
  symmetrify_star u ⟨v, sum.inr e⟩ = sum.inr ⟨v, e⟩ := rfl

@[simps]
def symmetrify_costar (u : U) : costar (symmetrify.of.obj u) ≃ costar u ⊕ star u :=
begin
  fsplit,
  { rintro ⟨v,(f|g)⟩, exact sum.inl ⟨v,f⟩, exact sum.inr ⟨v,g⟩, },
  { rintro (⟨v,f⟩|⟨v,g⟩), exact ⟨v,quiver.hom.to_pos f⟩, exact ⟨v,quiver.hom.to_neg g⟩, },
  { rintro ⟨v,(f|g)⟩, simp, },
  { rintro (⟨v,f⟩|⟨v,g⟩), simp, },
end

lemma prefunctor.symmetrify_star (u : U) : (φ.symmetrify.star u) =
 (symmetrify_star (φ.obj u)).symm ∘ (sum.map (φ.star u) (φ.costar u)) ∘ (symmetrify_star u) :=
begin
  rw equiv.eq_symm_comp,
  ext e', cases e' with v e, cases e;
  simp,
end

lemma prefunctor.symmetrify_costar (u : U) : (φ.symmetrify.costar u) =
 (symmetrify_costar (φ.obj u)).symm ∘ (sum.map (φ.costar u) (φ.star u)) ∘ (symmetrify_costar u) :=
begin
  rw equiv.eq_symm_comp,
  ext e, cases e with v e, cases e;
  simp,
end

lemma is_covering.symmetrify (hφ : φ.is_covering) : φ.symmetrify.is_covering :=
begin
  split;
  rintro u,
  { rw φ.symmetrify_star u,
    simp only [equiv_like.comp_bijective, equiv_like.bijective_comp],
    exact ⟨function.injective.sum_map (hφ.left u).left (hφ.right u).left,
         function.surjective.sum_map (hφ.left u).right (hφ.right u).right⟩, },
  { rw φ.symmetrify_costar u,
    simp only [equiv_like.comp_bijective, equiv_like.bijective_comp],
    exact ⟨function.injective.sum_map (hφ.right u).left (hφ.left u).left,
         function.surjective.sum_map (hφ.right u).right (hφ.left u).right⟩, },
end

@[reducible] def path_from (u : U) := Σ v : U, path u v

def prefunctor.path_from (u : U) : path_from u → path_from (φ.obj u) :=
λ p, ⟨φ.obj p.1, φ.map_path p.2⟩

@[simp] lemma prefunctor.path_from_apply {u v : U} (p : path u v) :
  φ.path_from u ⟨v, p⟩ = ⟨φ.obj v, φ.map_path p⟩ := rfl

lemma prefunctor.path_from_bijective (hφ : φ.is_covering) (u : U) :
  function.bijective (φ.path_from u) := sorry
