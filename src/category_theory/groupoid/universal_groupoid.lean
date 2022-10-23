/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import category_theory.category.basic
import category_theory.functor.basic
import category_theory.groupoid
import category_theory.groupoid.basic
import combinatorics.quiver.basic
import combinatorics.quiver.symmetric
import logic.relation
import tactic.nth_rewrite
import category_theory.path_category
import category_theory.quotient
import category_theory.groupoid.vertex_group

/-!
# Universal groupoid

This file defines the universal groupoid of a groupoid along a function. to its unique

-/

namespace category_theory

namespace groupoid

namespace universal

universes u v u' v' u'' v''

variables {V : Type u} [groupoid V] {V' : Type u'} (σ : V → V')

local postfix ` * ` := quiver.push.of

/-- Two reduction steps possible: compose composable arrows, or drop identity arrows -/
inductive red_step : hom_rel (paths (quiver.push σ))
| comp (X Y Z : V) (f : X ⟶ Y) (g : Y ⟶ Z) :
    red_step
      ((σ *).map (f ≫ g)).to_path
      (((σ *).map f).to_path ≫ ((σ *).map g).to_path)
| id (X : V) :
    red_step
      (𝟙 $ σ X)
      ((σ *).map $ 𝟙 X).to_path

/-- The underlying vertices of the universal groupoid -/
def _root_.category_theory.groupoid.universal_groupoid
  {V : Type u} [groupoid V] {V' : Type u'} (σ : V → V') := quotient (red_step σ)

instance : category (universal_groupoid σ) := quotient.category (red_step σ)

lemma congr_reverse {X Y : paths $ quiver.push σ} (p q : X ⟶ Y) :
  quotient.comp_closure (red_step σ) p q →
  quotient.comp_closure (red_step σ) (p.reverse) (q.reverse)  :=
begin
  rintros ⟨U, W, XW, pp, qq, WY, (⟨x, y, z, f, g⟩|(x))⟩,
  --rcases rs with (⟨x, y, z, f, g⟩|⟨x⟩),
  { have : quotient.comp_closure
      (red_step σ)
      (WY.reverse
        ≫ (((σ *)).map (quiver.reverse $ f≫g)).to_path
          ≫  XW.reverse)
      (WY.reverse ≫ ((((σ *)).map (quiver.reverse g)).to_path
        ≫ (((σ *)).map (quiver.reverse f)).to_path)
          ≫ XW.reverse),
    { apply quotient.comp_closure.intro,
      have := @red_step.comp _ _ _ σ (z) (y) (x) (inv g) (inv f),
      simpa only [reverse_eq_inv, inv_eq_inv, is_iso.inv_comp] using this, },
    simpa only [category_struct.comp, quiver.path.reverse, quiver.path.reverse_comp,
                quiver.push.of_reverse, reverse_eq_inv,
                inv_eq_inv, is_iso.inv_comp, quiver.path.comp_nil, quiver.path.comp_assoc,
                quiver.path.reverse_to_path] using this, },
  { have : quotient.comp_closure
      (red_step σ)
      (WY.reverse ≫ 𝟙 _ ≫  XW.reverse)
      (WY.reverse ≫ (((σ *)).map (𝟙 x)).to_path ≫ XW.reverse),
    { apply quotient.comp_closure.intro,
      have := @red_step.id _ _ _ σ  (x),
      simpa only [reverse_eq_inv, inv_eq_inv, is_iso.inv_comp] using this, },
    simpa only [category_struct.comp, category_struct.id, quiver.path.reverse,
                quiver.path.reverse_comp, quiver.push.of_reverse,
                reverse_eq_inv, inv_eq_inv, is_iso.inv_id, quiver.path.comp_nil,
                quiver.path.comp_assoc, quiver.path.nil_comp] using this, },

end

lemma congr_comp_reverse {X Y : paths $ quiver.push σ} (p : X ⟶ Y) :
  quot.mk (@quotient.comp_closure _ _ (red_step σ) _ _) (p ≫ p.reverse) =
  quot.mk (@quotient.comp_closure _ _ (red_step σ) _ _) (𝟙 X) :=
begin
  apply quot.eqv_gen_sound,
  induction p with _ _ q f ih,
  { apply eqv_gen.refl, },
  { rcases f with ⟨x,y,f⟩,
    simp only [quiver.path.reverse],
    fapply eqv_gen.trans,
    { exact q ≫ (q.reverse),},
    { apply eqv_gen.symm,
      fapply eqv_gen.trans,
      { exact q ≫ ((σ *).map (𝟙 x)).to_path ≫ q.reverse, },
      { have : ((paths.category_paths (quiver.push σ)).id $ σ x) ≫ q.reverse = q.reverse, by simp,
        nth_rewrite_lhs 0 ←this,
        apply eqv_gen.rel, constructor, constructor, },
      { apply eqv_gen.rel,
        have : quotient.comp_closure
               (red_step σ)
               (q ≫ (σ * .map $ f ≫ inv f).to_path ≫ q.reverse)
               (q ≫ ((σ * .map f).to_path ≫ (σ * .map $ inv f).to_path) ≫ q.reverse), by
        { apply quotient.comp_closure.intro, constructor, },
      dsimp only [category_struct.comp, quiver.hom.to_path,
                  quiver.path.comp, quiver.push.of, quiver.reverse, quiver.has_reverse.reverse'] at this ⊢,
      simpa only [←quiver.path.comp_assoc,quiver.path.comp_cons, quiver.path.comp_nil, inv_eq_inv,
                 is_iso.hom_inv_id] using this, -- UGLY
       }, },
    { exact ih }, },
end

lemma congr_reverse_comp {X Y : paths $ quiver.push σ} (p : X ⟶ Y) :
  quot.mk (@quotient.comp_closure _ _ (red_step σ) _ _) (p.reverse ≫ p) =
  quot.mk (@quotient.comp_closure _ _ (red_step σ) _ _) (𝟙 Y) :=
begin
  nth_rewrite 1 ←quiver.path.reverse_reverse p,
  apply congr_comp_reverse,
end

/-- The inverse of an arrow in the universal groupoid -/
def quot_inv {X Y : universal_groupoid σ} (f : X ⟶ Y) : Y ⟶ X :=
quot.lift_on f
            (λ pp, quot.mk _ $ pp.reverse)
            (λ pp qq con, quot.sound $ congr_reverse σ pp qq con)

instance : groupoid (universal_groupoid σ) :=
{ inv       := λ (X Y : universal_groupoid σ) (f : X ⟶ Y), quot_inv σ f,
  inv_comp' := λ X Y p, quot.induction_on p $ λ pp, congr_reverse_comp σ pp,
  comp_inv' := λ X Y p, quot.induction_on p $ λ pp, congr_comp_reverse σ pp }

/-- The extension of `σ` to a functor -/
def extend : V ⥤ (universal_groupoid σ) :=
{ obj := λ X, ⟨σ X⟩,
  map := λ X Y f, quot.mk _ (((σ *)).map f).to_path,
  map_id' := λ X, eq.symm $ quot.sound $ quotient.comp_closure.of _
    (𝟙 _)
    (σ * .map $ _).to_path
    (red_step.id X),
  map_comp' := λ X Y Z f g, quot.sound $ quotient.comp_closure.of _
    (σ * .map (f ≫ g)).to_path
    ((σ * .map f).to_path ≫ (σ * .map g).to_path)
    (red_step.comp X Y Z f g) }

def as : (universal_groupoid σ) → V' := λ x, x.as
lemma extend_eq : (extend σ).to_prefunctor =
  ((quiver.push.of σ).comp paths.of).comp (quotient.functor $ red_step σ).to_prefunctor := rfl

lemma _root_.category_theory.functor.to_prefunctor_ext {C D : Type*} [category C] [category D]
  (F G : C ⥤ D) : F = G ↔ F.to_prefunctor = G.to_prefunctor :=
begin
  split, { rintros rfl, refl },
  intros h,
  have h1 : F.obj = G.obj,
  { show F.to_prefunctor.obj = G.to_prefunctor.obj,
    exact congr_arg prefunctor.obj h },
  cases F, cases G, cases h1,
  congr, ext A B f,
  simpa using congr_arg_heq (λ e : prefunctor C D, e.map f) h,
end


section ump

variables {V'' : Type*} [groupoid V'']
  (θ : V ⥤ V'') (τ₀ : V' → V'') (hτ₀ : ∀ x, θ.obj x = τ₀ (σ x))

/--
Any functor `θ` from `V` to a groupoid `V''` with `θ.obj` factoring through `σ`
defines a functor from `V'`.
 -/
def lift : (universal_groupoid σ) ⥤ V'' :=
quotient.lift _
  ( paths.lift $ quiver.push.lift σ θ.to_prefunctor τ₀ hτ₀ )
  ( λ _ _ _ _ h, by
    { dsimp only [paths.lift, quiver.push.lift],
      induction h,
      { dsimp [quiver.push.of, category_struct.comp, category_struct.id, quiver.hom.to_path],
        simp only [functor.map_comp, cast_cast, category.id_comp],
        apply eq_of_heq,
        apply (cast_heq _ _).trans,
        congr, any_goals { apply hτ₀ },
        all_goals { symmetry, simp only [cast_heq], }, },
      { dsimp [quiver.push.of, category_struct.comp, category_struct.id, quiver.hom.to_path],
        simp only [functor.map_id, cast_cast, category.id_comp],
        apply eq_of_heq,
        symmetry,
        apply (cast_heq _ _).trans,
        rw hτ₀, }, } )

lemma lift_spec_obj : (lift σ θ τ₀ hτ₀).obj = τ₀ ∘ (as σ) := rfl

lemma lift_spec_comp : (extend σ) ⋙ (lift σ θ τ₀ hτ₀) = θ :=
begin
  rw [functor.to_prefunctor_ext,←functor.to_prefunctor_comp, extend_eq],
  dsimp only [lift],
  rw [prefunctor.comp_assoc, functor.to_prefunctor_comp, quotient.lift_spec,
      prefunctor.comp_assoc, paths.lift_spec, quiver.push.lift_spec_comm],
end

lemma lift_unique (Φ : universal_groupoid σ ⥤ V'')
  (Φ₀ : Φ.obj = τ₀∘(as σ)) (Φc : extend σ ⋙ Φ = θ) : Φ = (lift σ θ τ₀ hτ₀) :=
begin
  apply quotient.lift_unique,
  apply paths.lift_unique,
  apply quiver.push.lift_unique,
  { ext,
    simp only [prefunctor.comp_obj, paths.of_obj, functor.to_prefunctor_obj, functor.comp_obj],
    rw Φ₀, refl, },
  { rw [functor.to_prefunctor_ext, ←functor.to_prefunctor_comp] at Φc,
    exact Φc, },
end

end ump

section composite
/-!
Given `σ : V → V'` and `τ : V' → V''`, and `[groupoid V]`, taking the universal groupoid along
`τ∘σ` is equivalent to first taking it along `σ`, and then along `τ`.
-/
variables {V'' : Type*} (τ : V' → V'')

end composite

section universal_group
/-!
The universal group is the universal groupoid for the constant map to a singleton type.
-/

def _root_.category_theory.groupoid.universal_group.groupoid (V : Type*) [groupoid V] :=
@universal_groupoid V _ unit (λ (X : V), unit.star)

instance (V : Type*) [groupoid V] : groupoid (universal_group.groupoid V) :=
category_theory.groupoid.universal_groupoid.category_theory.groupoid (λ (X : V), unit.star)

def _root_.category_theory.groupoid.universal_group.star  (V : Type*) [groupoid V] :
  universal_group.groupoid V := ⟨unit.star⟩

def _root_.category_theory.groupoid.universal_group :=
  (universal_group.star V) ⟶ (universal_group.star V)

namespace group



def lift :

end group

end universal_group

end universal

end groupoid

end category_theory
