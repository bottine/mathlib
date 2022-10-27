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
import tactic.induction


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
local notation σ ` † ` f := ((σ *).map f).to_path

/-- Two reduction steps possible: compose composable arrows, or drop identity arrows -/
inductive red.atomic_step : hom_rel (paths (quiver.push σ))
| comp (X Y Z : V) (f : X ⟶ Y) (g : Y ⟶ Z) :
    red.atomic_step
      ((σ † f) ≫ (σ † g))
      (σ † (f ≫ g))
| id (X : V) :
    red.atomic_step
      (σ † (𝟙 X))
      (𝟙 $ σ X)

def red.step {X Y : paths $ quiver.push σ} (p q : X ⟶ Y) :=
  quotient.comp_closure (red.atomic_step σ) p q

/-- The underlying vertices of the universal groupoid -/
def _root_.category_theory.groupoid.universal_groupoid
  {V : Type u} [groupoid V] {V' : Type u'} (σ : V → V') := quotient (red.atomic_step σ)

instance : category (universal_groupoid σ) := quotient.category (red.atomic_step σ)

lemma congr_reverse {X Y : paths $ quiver.push σ} (p q : X ⟶ Y) :
  red.step σ p q → red.step σ (p.reverse) (q.reverse) :=
begin
  rintros ⟨U, W, XW, pp, qq, WY, (⟨x, y, z, f, g⟩|(x))⟩,
  { have : red.step σ
      (WY.reverse ≫ ((σ † (quiver.reverse g))
        ≫ (σ † (quiver.reverse f)))
          ≫ XW.reverse)
      (WY.reverse
        ≫ (σ † (quiver.reverse $ f≫g))
          ≫  XW.reverse),
    { apply quotient.comp_closure.intro,
      have := @red.atomic_step.comp _ _ _ σ (z) (y) (x) (inv g) (inv f),
      simpa only [reverse_eq_inv, inv_eq_inv, is_iso.inv_comp] using this, },
    simpa only [category_struct.comp, quiver.path.reverse, quiver.path.reverse_comp,
                quiver.push.of_reverse, reverse_eq_inv,
                inv_eq_inv, is_iso.inv_comp, quiver.path.comp_nil, quiver.path.comp_assoc,
                quiver.path.reverse_to_path] using this, },
  { have : red.step σ
      (WY.reverse ≫ (σ † (𝟙 x)) ≫ XW.reverse)
      (WY.reverse ≫ 𝟙 _ ≫  XW.reverse),
    { apply quotient.comp_closure.intro,
      have := @red.atomic_step.id _ _ _ σ  (x),
      simpa only [reverse_eq_inv, inv_eq_inv, is_iso.inv_comp] using this, },
    simpa only [category_struct.comp, category_struct.id, quiver.path.reverse,
                quiver.path.reverse_comp, quiver.push.of_reverse,
                reverse_eq_inv, inv_eq_inv, is_iso.inv_id, quiver.path.comp_nil,
                quiver.path.comp_assoc, quiver.path.nil_comp] using this, },

end

lemma congr_comp_reverse {X Y : paths $ quiver.push σ} (p : X ⟶ Y) :
  quot.mk (@red.step _ _ _ σ _ _) (p ≫ p.reverse) =
  quot.mk (@red.step _ _ _ σ _ _) (𝟙 X) :=
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
        apply eqv_gen.symm, apply eqv_gen.rel, constructor, constructor, },
      { apply eqv_gen.symm, apply eqv_gen.rel,
        have : red.step σ
               (q ≫ ((σ † f) ≫ (σ † (inv f))) ≫ q.reverse)
               (q ≫ (σ † (f ≫ inv f)) ≫ q.reverse), by
        { apply quotient.comp_closure.intro, constructor, },
      dsimp only [category_struct.comp, quiver.hom.to_path,
                  quiver.path.comp, quiver.push.of, quiver.reverse, quiver.has_reverse.reverse'] at this ⊢,
      simpa only [←quiver.path.comp_assoc,quiver.path.comp_cons, quiver.path.comp_nil, inv_eq_inv,
                 is_iso.hom_inv_id] using this,
       }, },
    { exact ih, }, },
end

lemma congr_reverse_comp {X Y : paths $ quiver.push σ} (p : X ⟶ Y) :
  quot.mk (@red.step _ _ _ σ _ _) (p.reverse ≫ p) =
  quot.mk (@red.step _ _ _ σ _ _) (𝟙 Y) :=
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
  map_id' := λ X, quot.sound $ quotient.comp_closure.of _ _ _ (red.atomic_step.id X),
  map_comp' := λ X Y Z f g, eq.symm $ quot.sound $
    quotient.comp_closure.of _ _ _ (red.atomic_step.comp X Y Z f g) }

/-- Get the original vertex. -/
abbreviation as : (universal_groupoid σ) → V' := λ x, x.as

lemma extend_eq : (extend σ).to_prefunctor =
  ((quiver.push.of σ).comp paths.of).comp (quotient.functor $ red.atomic_step σ).to_prefunctor := rfl

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
        symmetry,
        apply (cast_heq _ _).trans,
        congr,
        any_goals { apply hτ₀ },
        all_goals { symmetry, simp only [cast_heq], }, },
      { dsimp [quiver.push.of, category_struct.comp, category_struct.id, quiver.hom.to_path],
        simp only [functor.map_id, cast_cast, category.id_comp],
        apply eq_of_heq,
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

open relation

variables {X Y : paths $ quiver.push σ} (p q r : X ⟶ Y)

-- we defined it the wrong way round
abbreviation red.step_refl (p q : X ⟶ Y) : Prop := refl_gen (red.step σ) p q
abbreviation red (p q : X ⟶ Y) : Prop := refl_trans_gen (red.step σ) p q
abbreviation red.symm (p q : X ⟶ Y) : Prop := join (red σ) p q

lemma red_step_iff :
  red.atomic_step σ p q ↔
  (∃ (x z y : V) (f : x ⟶ z) (g : z ⟶ y) (xX : σ x = X) (yY : σ y = Y),
    q = (eq_to_hom xX.symm) ≫ (σ † (f ≫ g)) ≫ (eq_to_hom yY) ∧
    p = (eq_to_hom xX.symm) ≫ ((σ †  f) ≫ (σ †  g)) ≫ (eq_to_hom yY)) ∨
  (∃ (x : V) (xX : σ x = X) (XY : X = Y),
    q = eq_to_hom XY ∧
    p = (eq_to_hom xX.symm) ≫ ((σ *).map $ 𝟙 x).to_path ≫ (eq_to_hom $ xX.trans XY))  :=
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
    { simp only [eq_to_hom_refl, category.comp_id, category.id_comp], constructor, },
    { constructor, }, },
end

lemma red.atomic_step_length (h : red.atomic_step σ p q) :
  p.length = q.length.succ := by { cases h; refl, }

lemma red.step_length (h : red.step σ p q ) : p.length = q.length.succ :=
begin
  cases h,
  simp only [quiver.path.length_comp, category_struct.comp, red.atomic_step_length σ _ _ h_h,
             nat.succ_add],
  refl,
end

lemma red.step_length_lt (h : red.step σ p q) : q.length < p.length := by
{ rw red.step_length σ p q h, exact lt_add_one (quiver.path.length q), }

lemma red.step_not_nil (s t : X ⟶ X) : red.step σ s t → s ≠ quiver.path.nil :=
begin
  rintro h, cases h, cases h_h;
  { rintro h,
    let := congr_arg (quiver.path.length) h,
    simpa [category_struct.comp] using this, },
end

section diamond_helper

open quiver.path

lemma red.step_diamond_comp_comp :
∀ {a b : paths $ quiver.push σ} {X Y Z : V} {X' Y' Z' : V}
  {pre : a ⟶ σ X} {f : X ⟶ Y} {g : Y ⟶ Z} {suf : σ Z ⟶ b}
  {pre' : a ⟶ σ X'} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'} {suf' : σ Z' ⟶ b},
  pre ≫ ((σ † f) ≫ (σ † g)) ≫ suf = pre' ≫ ((σ † f') ≫ (σ † g')) ≫ suf'
→ pre ≫ (σ † (f ≫ g)) ≫ suf = pre' ≫ (σ † (f' ≫ g')) ≫ suf' ∨
  ∃ p, red.step σ (pre ≫ (σ † (f ≫ g)) ≫ suf) p ∧
       red.step σ (pre' ≫ (σ † (f' ≫ g')) ≫ suf') p := sorry

lemma red.step_diamond_comp_nil : ∀ {a b : paths $ quiver.push σ} {X Y Z W : V}
  {pre : a ⟶ σ X} {f : X ⟶ Y} {g : Y ⟶ Z} {suf : σ Z ⟶ b}
  {pre' : a ⟶ σ W} {suf' : σ W ⟶ b},
  pre ≫ ((σ † f) ≫ (σ † g)) ≫ suf = pre' ≫ (σ † 𝟙 W) ≫ suf'
→ ∃ p, red.step σ (pre ≫ (σ † (f ≫ g)) ≫ suf) p ∧
       red.step σ (pre' ≫ (𝟙 $ σ W) ≫ suf') p := sorry

lemma red.step_diamond_nil_nil : ∀ {a b : paths $ quiver.push σ} {W W' : V}
  {pre : a ⟶ σ W} {suf : σ W ⟶ b}
  {pre' : a ⟶ σ W'} {suf' : σ W' ⟶ b},
  pre ≫ (σ † 𝟙 W) ≫ suf = pre' ≫ (σ † 𝟙 W') ≫ suf' →
  pre ≫ (𝟙 $ σ W) ≫ suf = pre' ≫ (𝟙 $ σ W') ≫ suf' ∨
  ∃ p, red.step σ (pre ≫ (𝟙 $ σ _) ≫ suf) p ∧
       red.step σ (pre' ≫ (𝟙 $ σ _) ≫ suf') p :=
begin
  rintros a b W W' pre suf pre' suf',
  induction' pre,
end

end diamond_helper

lemma diamond : ∀ {X Y} (r p q : X ⟶ Y),
  red.step σ r p → red.step σ r q → p = q ∨ ∃ s, red.step σ p s ∧ red.step σ q s :=
begin
  rintro X Y r p q ⟨ap,bp,prep,mp,mp',sufp,hp⟩ rq,
  induction' rq with aq bq preq mq mq' sufq hq,
  induction' hp,
  { induction' hq,
    { obtain e|⟨h,r⟩ := red.step_diamond_comp_comp σ induction_eq_4,
      { left, exact e.symm, },
      { right, exact ⟨h,r.symm⟩, }, },
    { right, exact red.step_diamond_comp_nil σ induction_eq_4.symm, }, },
  { induction' hq,
    { right,
      obtain ⟨h,l,r⟩:= red.step_diamond_comp_nil σ induction_eq_4,
      exact ⟨h,r,l⟩, },
    { obtain e|⟨h,r,l⟩ := red.step_diamond_nil_nil σ induction_eq_4,
      { left, exact e.symm, },
      { right, exact ⟨h,l,r⟩, }, }  },
end

lemma diamond' : red.step σ r p → red.step σ r q → ∃ s, red.step_refl σ p s ∧ red σ q s :=
begin
  rintro pq pr,
  rcases diamond σ _ _ _ pq pr with (rfl|⟨s,qs,rs⟩),
  { use p, split, constructor, constructor, },
  { exact ⟨s,refl_gen.single qs,refl_trans_gen.single rs⟩, },
end

lemma church_rosser : red σ r p → red σ r q → ∃ s, red σ p s ∧ red σ q s :=
begin
  refine church_rosser _,
  rintro p q r pq pr,
  exact diamond' σ _ _ _ pq pr,
end

def is_reduced := ¬ ∃ (q : X ⟶ Y), red.step σ p q

lemma red.equal_of_is_reduced : red σ p q → is_reduced σ p → p = q :=
begin
  rintro pq pred,
  rcases pq.cases_head with (rfl|⟨r,pr,rq⟩),
  { refl, },
  { apply (pred ⟨r,pr⟩).elim, },
end

-- maybe should be done using `wf.fix` ?
 lemma red.exists_is_reduced : ∀ (p : X ⟶ Y), ∃ (r : X ⟶ Y), (red σ p r ∧ is_reduced σ r)
| p := if h : is_reduced σ p then ⟨p, by {apply refl_trans_gen.refl}, h⟩ else by
  { dsimp [is_reduced] at h, push_neg at h,
    obtain ⟨q,qp⟩ := h,
    let : q.length < p.length := red.step_length_lt σ p q qp, -- hint for well-foundedness
    obtain ⟨r, rq, rred⟩ := red.exists_is_reduced q,
    refine ⟨r, _, rred⟩,
    exact refl_trans_gen.trans (refl_trans_gen.single qp) rq, }
using_well_founded
{ dec_tac := `[assumption],
  rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ (f : X ⟶ Y), f.length)⟩] }

lemma red.unique_reduced : red σ p q → red σ p r → is_reduced σ q → is_reduced σ r → q = r :=
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

lemma red.symm_of_eqv_gen : eqv_gen (red.step σ) p q → red.symm  σ p q :=
begin
  rintro h,
  have equiv : _root_.equivalence (@red.symm  _ _ _ σ X Y) :=
    equivalence_join_refl_trans_gen (λ a b c, diamond' σ _ _ _),
  have le : ∀ (f g : X ⟶ Y), red.step σ f g → red.symm  σ f g := λ f g h',
    join_of_single reflexive_refl_trans_gen (refl_trans_gen.single h'),
  let h' := eqv_gen.mono le h,
  rw (equivalence.eqv_gen_eq equiv) at h',
  exact h',
end

lemma red.eqv_gen : red σ p q → eqv_gen (red.step σ) p q :=
begin
  rintro h,
  induction h with _ _ _ r ih,
  { apply eqv_gen.refl p, },
  { apply eqv_gen.trans, exact ih, apply eqv_gen.rel, exact r, },
end

lemma unique_reduced' : eqv_gen (red.step σ) p q → is_reduced σ p → is_reduced σ q → p = q :=
begin
  rintro h pred qred,
  have h' : red.symm  σ p q := red.symm_of_eqv_gen σ p q h,
  rcases h' with ⟨d,pd,qd⟩,
  rw [red.equal_of_is_reduced σ _ _ pd pred, red.equal_of_is_reduced σ _ _ qd qred],
end

lemma unique_reduced {X Y : universal_groupoid σ} (p : X ⟶ Y) :
  ∃! (f : X.as ⟶ Y.as), is_reduced σ f ∧ quot.mk _ f = p :=
begin
  apply quot.induction_on p,
  rintro f, apply exists_unique_of_exists_of_unique,
  { let g := (red.exists_is_reduced σ f).some,
    obtain ⟨fg, gred⟩ := (red.exists_is_reduced σ f).some_spec,
    refine ⟨g,gred,_⟩,
    apply quot.eqv_gen_sound,
    apply eqv_gen.symm,
    apply red.eqv_gen,
    exact fg, },
  { rintros g h ⟨gred,geq⟩ ⟨hred,heq⟩,
    have := quot.exact _ (geq.trans heq.symm),
    exact unique_reduced' σ g h this gred hred, },
end

lemma push_arrow_red {x y : V} (f : x ⟶ y) :
  (∃ q, red.step σ (σ † f) q) → (∃ h : x = y, f = eq_to_hom h) :=
begin
  rintro ⟨q,fq⟩,
  induction' fq,
  induction' h;
  simp [quiver.hom.to_path, category_struct.comp, quiver.path.comp] at induction_eq_4;
  let := congr_arg quiver.path.length induction_eq_4;
  simp [quiver.path.length_cons] at this,
  { sorry, /- `this` is impossible -/ },
  { sorry,/- the equality of length should force `f` to be nil-/}
end

lemma push_arrow_is_reduced {x y : V} (f : x ⟶ y) (hf : ¬ ∃ h : x = y, f = eq_to_hom h) :
  is_reduced σ (σ † f) :=
begin
  rintro ⟨q,fq⟩,
  let := red.step_length σ _ _ fq,
  simp [quiver.hom.to_path, quiver.path.length, nat.succ_eq_one_add] at this,
  let := quiver.path.nil_of_length_zero _ this,

  induction fq with a b pre p q suf rs,
  rw red_step_iff at rs,
  rcases rs with ⟨a,b,c,d,e,f,g,h,i⟩|⟨a,b,c,d,e⟩,
  { sorry, },
  { sorry, },
end


end reduced_words

lemma of_very_faithful {x y z w : V} (p : x ⟶ y) (q : z ⟶ w)
  (xz : (extend σ).obj x = (extend σ).obj z) (yw : (extend σ).obj y = (extend σ).obj w) :
  (extend σ).map p ≫ (eq_to_hom yw) = (eq_to_hom xz) ≫ (extend σ).map q →
  ∃ (h : x = y) (k : z = w) (l : x = y), p = eq_to_hom h ∧ q = eq_to_hom k :=
begin
  intro he,
  by_contra, push_neg at h, sorry
end

end universal
end groupoid
end category_theory
