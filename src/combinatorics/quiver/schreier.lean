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

variables {V : Type*} [quiver.{v+1} V] {U : Type*} [quiver.{u+1} U] {W : Type*} [quiver.{w+1} W]

instance iso_group : group (V ≃q V) := sorry

section coloring

class coloring (V S : Type*) [quiver V] :=
(color : ∀ {u v : V}, (u ⟶ v) → S)

def color {V : Type*} (S : Type*) [quiver V] [coloring V S] {X Y : V} (f : X ⟶ Y) : S :=
coloring.color f

def color_preserving {V S : Type*} [quiver V] {V' S' : Type*} [quiver V']
  [coloring V S] [coloring V' S'] (σ : S → S') (F : V ⟶q V') :=
∀ {u v : V} (f : u ⟶ v), color S' (F.map f) = σ (color S f)

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

-- I'm getting confused trying to prove this
noncomputable def equiv_coset_graph [mul_action.is_pretransitive G V] (x₀ : V) :
  schreier_coset_graph ι (mul_action.stabilizer G x₀) ≃q schreier_graph V ι := sorry

lemma equiv_coset_graph.color_preserving [mul_action.is_pretransitive G V] (x₀ : V)
  {X Y : schreier_coset_graph ι (mul_action.stabilizer G x₀)} (f : X ⟶ Y) :
  color_preserving (@id S) (equiv_coset_graph ι x₀).to_prefunctor := sorry


end group_action

abbreviation cayley_graph {G : Type*} [group G] {S : Type*} (ι : S → G) := schreier_graph G ι

section cayley_graph

variables {G : Type*} [group G] {S : Type*} (ι : S → G)

def as_automorphism (g : G) : cayley_graph ι ≃q cayley_graph ι :=
{ obj := λ x, to_schreier_graph G ι ((of_schreier_graph G ι x) * g⁻¹),
  bij_obj := by {dsimp [to_schreier_graph, of_schreier_graph], apply group.mul_right_bijective, },
  map := λ _ _ a, a.rec_on $ by
  { rintro s x,
    dsimp [to_schreier_graph, of_schreier_graph],
    change group.mul (ι s) x with (ι s) * x,
    rw mul_assoc,
    constructor, },
  bij_map := λ X Y, by
  { dsimp [to_schreier_graph, of_schreier_graph], sorry, } }

lemma as_automorphism.color_preserving (g : G) :
  color_preserving (@id S) (as_automorphism ι g).to_prefunctor := sorry

def as_automorphism_group : G →* (cayley_graph ι ≃q cayley_graph ι) :=
{ to_fun := as_automorphism ι,
  map_one' := by { dsimp [as_automorphism], ext, simp, },
  map_mul' := λ g g', by { dsimp [as_automorphism], ext, simp, } }

end cayley_graph

end schreier_graph

end quiver
