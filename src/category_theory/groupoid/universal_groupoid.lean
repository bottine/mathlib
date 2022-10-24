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
import tactic.rewrite_search
import category_theory.path_category
import category_theory.quotient
import category_theory.groupoid.vertex_group


/-!
# Universal groupoid

This file defines the universal groupoid of a groupoid along a function.

-/

open classical
local attribute [instance] prop_decidable


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
    { exact q ≫ (q.reverse), },
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
                 is_iso.hom_inv_id] using this,
       }, },
    { exact ih, }, },
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

/-- Get the original vertex. -/
abbreviation as : (universal_groupoid σ) → V' := λ x, x.as

lemma extend_eq : (extend σ).to_prefunctor =
  ((quiver.push.of σ).comp paths.of).comp (quotient.functor $ red_step σ).to_prefunctor := rfl

-- Thanks Adam Topaz
lemma _root_.category_theory.functor.to_prefunctor_ext {C D : Type*} [category C] [category D]
  (F G : C ⥤ D) : F = G ↔ F.to_prefunctor = G.to_prefunctor :=
begin
  split,
  { rintros rfl, refl },
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
        congr,
        any_goals { apply hτ₀ },
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

section reduced_words

variables {X Y : paths $ quiver.push σ} (p q r : X ⟶ Y)

-- we defined it the wrong way round
abbreviation R (p q : X ⟶ Y) : Prop := quotient.comp_closure (red_step σ) q p
abbreviation R' (p q : X ⟶ Y) : Prop := relation.refl_gen (R σ) p q
abbreviation RR (p q : X ⟶ Y) : Prop := relation.refl_trans_gen (R σ) p q
abbreviation RRR (p q : X ⟶ Y) : Prop := relation.join (RR σ) p q

lemma red_step_iff :
  red_step σ p q ↔
  (∃ (x z y : V) (f : x ⟶ z) (g : z ⟶ y) (xX : σ x = X) (yY : σ y = Y),
    p = (eq_to_hom xX.symm) ≫ ((σ *).map (f ≫ g)).to_path ≫ (eq_to_hom yY) ∧
    q = (eq_to_hom xX.symm) ≫ (((σ *).map f).to_path ≫ ((σ *).map g).to_path) ≫ (eq_to_hom yY)) ∨
  (∃ (x : V) (xX : σ x = X) (XY : X = Y),
    p = eq_to_hom XY ∧
    q = (eq_to_hom xX.symm) ≫ ((σ *).map $ 𝟙 x).to_path ≫ (eq_to_hom $ xX.trans XY))  :=
begin
  split,
  {
    rintros (⟨x, z, y, f, g⟩|(x)),
    { left, use [x,z,y,f,g,rfl,rfl],
      dsimp [quiver.push.of, quiver.hom.to_path],
      simp only [category.comp_id, category.id_comp, eq_self_iff_true, true_and], refl, },
    { right, use [x,rfl,rfl],
      dsimp [quiver.push.of, quiver.hom.to_path],
      simp only [category.comp_id, category.id_comp, eq_self_iff_true, and_true], refl, }, },
  { rintros (⟨x, z, y, f, g, rfl, rfl, rfl, rfl⟩|⟨x, rfl, rfl, rfl, rfl⟩),
    { constructor, },
    { constructor, }, },
end

lemma red_step_length (h : red_step σ p q) :
  p.length.succ = q.length := by { cases h; refl, }

lemma comp_closure_red_step_length
 (h : R σ q p ) : p.length.succ = q.length :=
begin
  cases h,
  simp only [quiver.path.length_comp, category_struct.comp, ←red_step_length σ _ _ h_h,
             nat.succ_add],
  refl,
end

lemma comp_closure_red_step_len_lt
 (h : R σ q p) : p.length < q.length := by
{ rw ←comp_closure_red_step_length σ p q h, exact lt_add_one (quiver.path.length p), }


lemma diamond : R σ r p → R σ r q → ∃ s, R σ p s ∧ R σ q s := sorry
lemma diamond' : R σ r p → R σ r q → ∃ s, R' σ p s ∧ RR σ q s :=
begin
  rintro pq pr,
  obtain ⟨s,qs,rs⟩ := diamond σ _ _ _ pq pr,
  exact ⟨s,relation.refl_gen.single qs,relation.refl_trans_gen.single rs⟩,
end


lemma church_rosser : RR σ r p → RR σ r q → ∃ s, RR σ p s ∧ RR σ q s :=
begin
  refine relation.church_rosser _,
  rintro p q r pq pr,
  exact diamond' σ _ _ _ pq pr,
end

def is_reduced := ¬ ∃ (q : X ⟶ Y), R σ p q

lemma equal_of_is_reduced : RR σ p q → is_reduced σ p → p = q :=
begin
  rintro pq pred,
  rcases pq.cases_head with (rfl|⟨r,pr,rq⟩),
  { refl, },
  { apply (pred ⟨r,pr⟩).elim, },
end

-- maybe should be done using `wf.fix` ?
lemma exists_reduced : ∀ (p : X ⟶ Y),
  ∃ (r : X ⟶ Y), RR σ p r ∧ is_reduced σ r
| p := if h : is_reduced σ p then ⟨p, by {apply relation.refl_trans_gen.refl}, h⟩ else by
  { dsimp [is_reduced] at h, push_neg at h,
    obtain ⟨q,qp⟩ := h,
    let hl : q.length < p.length := comp_closure_red_step_len_lt σ q p qp, -- hint for well-foundedness
    obtain ⟨r, rq, rred⟩ := exists_reduced q,
    refine ⟨r, _, rred⟩,
    refine relation.refl_trans_gen.trans _ rq, apply relation.refl_trans_gen.single, apply qp, }
using_well_founded
{ dec_tac := `[assumption],
  rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ (f : X ⟶ Y), f.length)⟩] }

lemma unique_reduced_down : RR σ p q → RR σ p r → is_reduced σ q → is_reduced σ r → q = r :=
begin
  rintros pq pr qred rred,
  obtain ⟨s,qs,rs⟩ := church_rosser σ _ _ _ pq pr,
  rcases qs.cases_head with (rfl|⟨t,qt,ts⟩);
  rcases rs.cases_head with (rfl|⟨u,ru,us⟩),
  { refl, },
  { apply (rred ⟨u,ru⟩).elim, },
  { apply (qred ⟨t,qt⟩).elim, },
  { apply (qred ⟨t,qt⟩).elim, },
end

lemma unique_reduced : eqv_gen (R σ) p q → is_reduced σ p → is_reduced σ q → p = q :=
begin
  rintro h pred qred,
  -- A boring bit of gymnastic to get `RRR` from `eqv_gen`…
  have equiv : _root_.equivalence (@RRR _ _ _ σ X Y) :=
    relation.equivalence_join_refl_trans_gen (λ a b c, diamond' σ _ _ _),
  have le : ∀ (f g : X ⟶ Y), R σ f g → RRR σ f g := λ f g h',
    relation.join_of_single relation.reflexive_refl_trans_gen (relation.refl_trans_gen.single h'),
  let h' := eqv_gen.mono le h,
  rw (equivalence.eqv_gen_eq equiv) at h',
  -- Now we have it
  rcases h' with ⟨d,pd,qd⟩,
  rw [equal_of_is_reduced σ _ _ pd pred, equal_of_is_reduced σ _ _ qd qred],
end

end reduced_words

end universal
end groupoid
end category_theory
