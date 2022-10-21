/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import category_theory.groupoid
import category_theory.groupoid.basic
import category_theory.groupoid.subgroupoid

/-!
# Quotient of a groupoid by a normal subgroupoid

This file defines the quotient of a groupoid by a normal (i.e. wide and closed under conjugation)
subgroupoid, and proves the associated universal property of the quotient.

## Main results


## Implementation notes

-/

namespace category_theory

open subgroupoid
open groupoid

universes u v

variables {C : Type u} [groupoid C] (S : subgroupoid C)

namespace quotient_groupoid

section isotropy
/-!
We first define what's here called “isotropy quotient”:
Given a normal subgroupoid `S`, this quotient is collapses all loops of `S`, i.e.
all vertex groups.
After quotienting by these vertex groups, the image of `S` in the quotient `is_graph_like`
which is easy to quotient out again.
-/

section cgr
/-!
Given a the wide subgroupoid `S`, two arrows `f g : c ⟶ d` are equivalent modulo the isotropy
groups of `S` iff there exist `γ : c ⟶ c` and `δ : d ⟶ d` both in `S` such that `g = γ ≫ f ≫ δ`.
This is an equivalence relation by wideness and since `S` is a subgroupoid.
-/

variables  (Sw : S.is_wide) {c d : C} (f g h : c ⟶ d)

def cgr (c) (d) (f) (g) := ∃ (γ ∈ S.arrows c c) (δ ∈ S.arrows d d), g = γ ≫ f ≫ δ

lemma cgr.refl (f : c ⟶ d) : cgr S c d f f :=  ⟨(𝟙 c), Sw.wide c, (𝟙 d), Sw.wide d, by simp ⟩
lemma cgr.symm {f g : c ⟶ d} : cgr S c d f g → cgr S c d g f :=
λ ⟨γ,hγ,δ,hδ,e⟩, ⟨inv γ, S.inv hγ, inv δ, S.inv hδ, by { rw e, simp, } ⟩
lemma cgr.tran {f g h : c ⟶ d} : cgr S c d f g → cgr S c d g h → cgr S c d f h :=
λ ⟨γ,hγ,δ,hδ,e⟩ ⟨δ',hδ',ε,hε,e'⟩,
⟨δ' ≫ γ, S.mul hδ' hγ, δ ≫ ε, S.mul hδ hε, by {rw [e',e], simp, }⟩

def cgr.setoid : setoid (c ⟶ d) :=
{ r := cgr S c d , iseqv := ⟨λ f, cgr.refl S Sw f, λ f g, cgr.symm S, λ f g h, cgr.tran S⟩ }

end cgr

def isotropy.quotient (S : subgroupoid C) (Sn : S.is_normal) := C

namespace isotropy

variable (Sn : S.is_normal)

instance : groupoid (isotropy.quotient S Sn) :=
{ hom := λ c d, quot (cgr S c d),
  id := λ c, quot.mk _ (𝟙 c),
  comp := λ a b c f g,
    quot.lift_on₂ f g
      ( λ f g, quot.mk (cgr S a c) (f ≫ g) )
      ( λ f g₁ g₂ ⟨γ,hγ,δ,hδ,e⟩,
        quot.sound ⟨(f ≫ γ ≫ inv f), Sn.conj' f hγ, δ, hδ, by { rw e, simp only [inv_eq_inv, category.assoc, is_iso.inv_hom_id_assoc], } ⟩ )
      ( λ f₁ f₂ g ⟨γ,hγ,δ,hδ,e⟩,
        quot.sound ⟨γ, hγ, (inv g ≫ δ ≫ g), Sn.conj g hδ, by { rw e, simp only [category.assoc, inv_eq_inv, is_iso.hom_inv_id_assoc], } ⟩ ),
  comp_id' := λ a b, by
    { refine quot.ind (λ f, _),
      simp only [quot.lift_on₂_mk, category.comp_id], },
  id_comp' := λ a b, by
    { refine quot.ind (λ f, _),
      simp only [quot.lift_on₂_mk, category.id_comp], },
  assoc' :=  λ a b c d f g h, by
    { refine quot.induction_on₃ f g h (λ f g h, _),
      simp only [quot.lift_on₂_mk, category.assoc],  },
  inv := λ a b f,
    quot.lift_on f
      ( λ f, quot.mk (cgr S b a) (inv f) )
      ( λ f₁ f₂ ⟨γ,hγ,δ,hδ,e⟩, quot.sound ⟨inv δ, S.inv hδ, inv γ, S.inv hγ, by { rw e, simp, } ⟩ ),
  comp_inv' := λ a b f, by
    { refine quot.induction_on f (λ f, _),
      simp only [quot.lift_on₂_mk, inv_eq_inv, is_iso.hom_inv_id], },
  inv_comp' := λ a b f, by
    { refine quot.induction_on f (λ f, _),
      simp only [quot.lift_on₂_mk, inv_eq_inv, is_iso.inv_hom_id], }, }

def of : C ⥤ (quotient S Sn) :=
{ obj := λ c, c,
  map := λ c d f, quot.mk _ f,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ _ _, rfl, }

lemma of_inj_on_objects : function.injective (of S Sn).obj := by { intros a b e, assumption }

lemma of_onto : im (of S Sn) (of_inj_on_objects S Sn) = (⊤ : subgroupoid $ quotient S Sn) :=
le_antisymm (le_top) $ λ ⟨c,d,f⟩ _, quot.induction_on f (λ f, by { constructor, constructor, })


/-- The image of `S` via the quotient is graph-like (since every loop is killed, essentially) -/
lemma map_is_graph_like : (map (of S Sn) (of_inj_on_objects S Sn) S).is_graph_like :=
begin
  rw subgroupoid.is_graph_like_iff,
  rintro c d,
  constructor,
  rintro ⟨_,hf⟩ ⟨_,hg⟩,
  cases hf,
  cases hg,
  simp only [subtype.mk_eq_mk],
  apply quot.sound,
  refine ⟨𝟙 _, Sn.wide _, inv hf_f ≫ hg_f, S.mul (S.inv _) _, _⟩,
  assumption,
  assumption,
  simp only [inv_eq_inv, is_iso.hom_inv_id_assoc, category.id_comp],
end

section ump
/-!
The universal mapping property of the quotient by the isotropy part of a normal subgroupoid.
-/

variables  {D : Type*} [groupoid D]
  (φ : C ⥤ D)
  (hφ : S.disconnect ≤ ker φ)

include hφ

/--
Given a morphism `φ : C ⥤ D` containing the isotropy part of `S` in its kernel, get a
morphism from the isotropy quotient.
-/
def lift : (quotient S Sn) ⥤ D :=
{ obj := λ c, φ.obj c,
  map := λ c d f,
    quot.lift_on f
      ( λ f, φ.map f )
      ( λ f₁ f₂ ⟨γ,hγ,δ,hδ,e⟩, by
        { rw subgroupoid.le_iff at hφ,
          let γ' : γ ∈ S.disconnect.arrows c c := by {constructor, exact hγ, },
          let hφγ := hφ γ',
          let δ' : δ ∈ S.disconnect.arrows d d := by {constructor, exact hδ, },
          let hφδ := hφ δ',
          simp only [mem_ker_iff, eq_self_iff_true,
                     exists_true_left] at hφγ hφδ,
          simp only [e, functor.map_comp, hφγ, hφδ, category.comp_id, category.id_comp,
                     eq_to_hom_refl], } ),
  map_id' := λ c, by
  { rw ←functor.map_id φ c, refl, },
  map_comp' := λ a b c f g, by
  { apply quot.induction_on₂ f g, rintros, rw ←functor.map_comp φ, refl, } }

lemma lift_spec : (of S Sn) ⋙ (lift S Sn φ hφ) = φ :=
begin
  apply functor.ext,
  { rintros, dsimp only [of, lift],
    simp only [functor.comp_map, eq_to_hom_refl, category.comp_id, category.id_comp], },
  { rintros, dsimp only [of, lift],
    simp only [functor.comp_obj], },
end

lemma lift_unique (Φ : (quotient S Sn) ⥤ D) (hΦ : (of S Sn) ⋙ Φ = φ) :
  Φ = (lift S Sn φ hφ) :=
begin
  subst_vars,
  apply functor.ext,
  { rintros, dsimp [of, lift],
    apply quot.induction_on f,
    rintro f,
    simp only [quot.lift_on_mk, functor.comp_map, category.comp_id, category.id_comp], },
  { rintros, dsimp only [of, lift], refl, }
end

end ump

/-- The kernel of the morphism `of S Sn : C ⥤ (quotient S Sn)` is exactly `S.disconnect`. -/
lemma ker_eq : ker (of S Sn) = S.disconnect :=
begin
  ext c d f,
  split,
  { rintro hf,
    rw mem_ker_iff at hf,
    obtain ⟨h,e⟩ := hf,
    rw mem_disconnect_iff,
    dsimp [of] at h e, subst h,
    simp only [eq_self_iff_true, true_and],
    have := @quotient.exact (c ⟶ c) (cgr.setoid S ⟨Sn.wide⟩) _ _ e,
    rcases cgr.symm S this with ⟨γ,hγ,δ,hδ,rfl⟩,
    apply S.mul hγ (S.mul (id_mem_of_tgt S hδ) hδ), },
  { rintro ⟨_,f,hf⟩,
    rw mem_ker_iff,
    refine ⟨rfl,_⟩,
    show quot.mk _ f = quot.mk _ (𝟙 _),
    apply quot.sound,
    refine ⟨inv f, S.inv hf, 𝟙 _, id_mem_of_tgt S hf,_⟩,
    simp only [inv_eq_inv, category.comp_id, is_iso.inv_hom_id], }
end


end isotropy

end isotropy

namespace graph_like
/-!
Quotient of a groupoid by a normal, graph-like subgroupoid.
By graph-likeness, the quotient be represented by the full subgroupoid induced by taking any
set of representatives of the vertices, which makes dealing with quotients easier.
-/

variables (Sw : S.is_wide)  (Sg : S.is_graph_like)


abbreviation r := λ c d, nonempty (S.arrows c d)

lemma r.refl (c : C) : r S c c := ⟨⟨𝟙 c, Sw.wide c⟩⟩
lemma r.symm {c d : C} : r S c d → r S d c := λ ⟨⟨f,fS⟩⟩, ⟨⟨inv f, S.inv fS⟩⟩
lemma r.tran {c d e : C} : r S c d → r S d e → r S c e := λ ⟨⟨f,fS⟩⟩ ⟨⟨g,gS⟩⟩, ⟨⟨f≫g, S.mul fS gS⟩⟩

def R : setoid C :=
{ r := r S ,  iseqv := ⟨λ _, r.refl S Sw _, λ _ _, r.symm S, λ _ _ _, r.tran S⟩ }

instance : setoid C := R S Sw

def reps : set C := set.range (@quotient.out C (R S Sw))

noncomputable def to_reps : C → reps S Sw :=
λ c,
⟨ @_root_.quotient.out C (R S Sw) (@_root_.quotient.mk C (R S Sw) c),
  ⟨ @_root_.quotient.mk C (R S Sw) c, rfl ⟩ ⟩

def of_reps : reps S Sw → C := λ c, c.val

lemma of_to_reps_congr (c : C) : (R S Sw).r (of_reps S Sw (to_reps S Sw c)) c :=
begin
  letI := R S Sw,
  change (of_reps S Sw (to_reps S Sw c)) ≈ c,
  apply quotient.exact,
  dsimp [of_reps, to_reps],
  rw quotient.out_eq,
end

noncomputable def to_reps_arrow (c : C) : of_reps S Sw (to_reps S Sw c)  ⟶ c :=
(of_to_reps_congr S Sw c).some.val

lemma to_reps_arrow_mem (c : C) :
  (to_reps_arrow S Sw c) ∈ (S.arrows (of_reps S Sw (to_reps S Sw c)) c) :=
(of_to_reps_congr S Sw c).some.prop

include Sg Sw
lemma to_reps_arrow_unique {c : C}
  {γ : of_reps S Sw (to_reps S Sw c) ⟶ c}
  (hγ : γ ∈ S.arrows (of_reps S Sw (to_reps S Sw c)) c) :
  γ = to_reps_arrow S Sw c :=
begin
  rw [subgroupoid.is_graph_like_iff, (is_wide_iff_objs_eq_univ S).mp Sw] at Sg,
  simp only [set.top_eq_univ, set.mem_univ, set.subsingleton_coe, set_coe.forall,
             forall_true_left] at Sg,
  apply Sg, exact hγ, apply to_reps_arrow_mem,
end
omit Sg Sw

lemma to_of_reps_eq (cc : reps S Sw) : (to_reps S Sw $ of_reps S Sw cc) = cc :=
begin
  dsimp [of_reps, to_reps],
  rcases cc with ⟨_,⟨x,rfl⟩⟩,
  simp only [subtype.coe_mk, quotient.out_eq, subtype.mk_eq_mk],
end

def quotient := (subgroupoid.full $ reps S Sw).objs

instance : groupoid (quotient S Sw) := (subgroupoid.full $ reps S Sw).coe

noncomputable def of : C ⥤ quotient S Sw :=
{ obj := λ c,
  ⟨ to_reps S Sw c,
    by { dsimp [quotient], rw full_objs, simp only [subtype.coe_prop], } ⟩,
  map := λ c d f,
    let
      γ := (to_reps_arrow S Sw c),
      δ := inv (to_reps_arrow S Sw d)
    in
      ⟨γ ≫ f ≫ δ, by { constructor; simp, } ⟩,
  map_id' := λ _, by
    { simp only [subtype.val_eq_coe, inv_eq_inv, category.id_comp, is_iso.hom_inv_id],
      refl, },
  map_comp' := λ x y z f g, by
    { ext, simp only [inv_eq_inv, category.assoc, subtype.coe_mk,
                      coe_to_category_comp_coe, is_iso.inv_hom_id_assoc], } }

def fo : (quotient S Sw) ⥤ C := subgroupoid.hom _

lemma of_fo_obj (c: quotient S Sw) : (of S Sw).obj ((fo S Sw).obj c) = c :=
begin
  dsimp [quotient] at c,
  rcases c with ⟨c',h⟩,
  rw mem_full_objs_iff at h,
  rcases h with ⟨_,rfl⟩,
  dsimp [of, fo, subgroupoid.hom, subgroupoid.full, to_reps],
  simp only [quotient.out_eq, subtype.mk_eq_mk],
end


private def ud {c d : quotient S Sw} (h : c ⟶ d) : c.val ⟶ d.val :=
begin
  exact h.val,
end

private lemma lol {c d : quotient S Sw} (h : c = d) :
  ud S Sw (eq_to_hom h) ∈ S.arrows c.val d.val :=
begin
  rcases h with rfl, simp,
  apply Sw.wide,
end

include Sg
lemma of_fo_map {c d : quotient S Sw} (f : c ⟶ d) :
  (of S Sw).map ((fo S Sw).map f)
= (eq_to_hom $ of_fo_obj S Sw c) ≫ f ≫ (eq_to_hom $ (of_fo_obj S Sw d).symm) :=
begin
  letI := R S Sw,
  dsimp only [quotient] at c d,
  rcases c with ⟨c',hc⟩,
  rcases d with ⟨d',hd⟩,
  rw mem_full_objs_iff at hc hd,
  rcases hc with ⟨c',rfl⟩,
  rcases hd with ⟨d',rfl⟩,
  dsimp only [of, fo, hom],
  let ec := of_fo_obj S Sw ⟨c'.out,hc⟩,
  let ed := of_fo_obj S Sw ⟨d'.out,hd⟩,
  congr,
  { change to_reps_arrow S Sw c'.out = ud S Sw (eq_to_hom ec),
    exact (to_reps_arrow_unique S Sw Sg (lol S Sw ec)).symm, },
  { change groupoid.inv (to_reps_arrow S Sw d'.out) = ud S Sw (eq_to_hom ed.symm),
    suffices : to_reps_arrow S Sw d'.out = inv (ud S Sw (eq_to_hom ed.symm)),
    { simp only [this, inv_eq_inv, is_iso.inv_inv], },
    symmetry,
    apply to_reps_arrow_unique S Sw Sg,
    apply S.inv, apply lol, }
end

lemma of_fo_eq_id : (fo S Sw) ⋙ (of S Sw) = functor.id _ :=
begin
  apply functor.ext,
  { rintro, simp only [functor.comp_map, functor.id_map], rw of_fo_map, exact Sg, },
end

lemma ker_eq : ker (of S Sw) = S :=
begin
  apply le_antisymm,
  { rw le_iff,
    rintro c d f hf,
    rw mem_ker_iff at hf,
    dsimp [of] at hf, --simp at hf,
    obtain ⟨h,e⟩ := hf,
    rw subtype.ext_iff at e,
    simp only [inv_eq_inv, subtype.coe_mk] at e,
    suffices :
      to_reps_arrow S Sw c ≫ f ≫ category_theory.inv (to_reps_arrow S Sw d) ∈
      S.arrows (of_reps S Sw (to_reps S Sw c)) (of_reps S Sw (to_reps S Sw d)),
    { apply mem_of_mul_mem S (to_reps_arrow S Sw c) f (to_reps_arrow_mem S Sw c),
      apply mem_of_mul_mem' S _ (category_theory.inv $ to_reps_arrow S Sw d),
      apply mem_of_inv_mem,
      simp only [inv_eq_inv, is_iso.inv_inv],
      apply to_reps_arrow_mem,
      simpa only [category.assoc] using this, },
    rw e, apply lol, },
  { rw le_iff,
    rintro c d f fS, sorry, }
end
omit Sg


section ump

variables {D : Type*} [groupoid D] (φ : C ⥤ D) (hφ : S ≤ ker φ)

def lift : quotient S Sw ⥤ D := (fo S Sw) ⋙ φ

include hφ
lemma lift_spec : (of S Sw) ⋙ (lift S Sw φ) = φ :=
begin
  dsimp only [lift, of, fo, subgroupoid.full, subgroupoid.hom],
  rw le_iff at hφ,
  fapply functor.ext,
  { rintro c,
    obtain ⟨γ,γS⟩ := (of_to_reps_congr S Sw c).some,
    let := hφ γS, rw mem_ker_iff at this,
    exact this.some, },
  { rintro c d f,
    simp only [subtype.val_eq_coe, inv_eq_inv, functor.comp_map,
               functor.map_comp, functor.map_inv],
    let hγ' := hφ (to_reps_arrow_mem S Sw c),
    let hδ' := hφ (to_reps_arrow_mem S Sw d),
    rw mem_ker_iff at hγ' hδ',
    obtain ⟨eγ,hγ''⟩ := hγ',
    obtain ⟨eδ,hδ''⟩ := hδ',
    simp only [subtype.coe_mk,hδ'',hγ'',inv_eq_to_hom], refl,  },
end

omit hφ
lemma _root_.category_theory.functor.map_eq_to_hom
  (C D : Type*) [category C] [category D] (F : C ⥤ D) (c c' : C) (h : c = c') :
  F.map (eq_to_hom h) = eq_to_hom (congr_arg F.obj h) :=
by { cases h, simp only [eq_to_hom_refl, functor.map_id], }

include hφ Sg
lemma lift_unique (Φ : quotient S Sw ⥤ D) (hΦ : (of S Sw) ⋙ Φ = φ) :
  Φ = (lift S Sw φ) :=
begin
  letI := R S Sw,
  subst_vars,
  dsimp [lift],
  rw le_iff at hφ,
  fapply functor.ext,
  { simp only [functor.comp_obj, set_coe.forall],
    rintro x h,
    rw of_fo_obj, },
  { simp only [set_coe.forall, functor.comp_map],
    rintro x h y k f,
    rw of_fo_map,
    simp only [functor.map_eq_to_hom, functor.map_comp, category.assoc, eq_to_hom_trans,
               eq_to_hom_refl, category.comp_id, eq_to_hom_trans_assoc, category.id_comp],
    exact Sg, },
end
omit Sg

end ump

end graph_like

section quotient
/-- The _actual_ quotient by `S`. -/

variable (Sn : S.is_normal)

def _root_.category_theory.quotient_groupoid :=
  graph_like.quotient
    (map (isotropy.of S Sn) (isotropy.of_inj_on_objects S Sn) S)
    (subgroupoid.is_normal_map
      S
      (isotropy.of S Sn)
      (isotropy.of_inj_on_objects S Sn)
      (isotropy.of_onto S Sn)
      Sn).to_is_wide

instance : groupoid (quotient_groupoid S Sn) :=
  graph_like.quotient.category_theory.groupoid
    (map /-(isotropy.of S Sn)-/ _ (isotropy.of_inj_on_objects S Sn) S)
    (is_normal_map
      /-S-/ _
      /-(isotropy.of S Sn)-/ _
      (isotropy.of_inj_on_objects S Sn)
      (isotropy.of_onto S Sn)
      Sn).to_is_wide


noncomputable def of :
C ⥤ quotient_groupoid S Sn := (isotropy.of _ _) ⋙ (graph_like.of _ _)

section ump

variables {D : Type*} [groupoid D] (φ : C ⥤ D) (hφ : S ≤ ker φ)

include hφ
def lift : quotient_groupoid S Sn ⥤ D :=
begin
  apply graph_like.lift,
  fapply isotropy.lift,
  exact φ,
  exact (disconnect_le S).trans hφ,
end

lemma lift_spec : (of S Sn) ⋙ (lift S Sn φ hφ) = φ :=
begin
  change isotropy.of S Sn ⋙ (graph_like.of (map (isotropy.of S Sn) _ S) _) ⋙
    graph_like.lift (map (isotropy.of S Sn) _ S) _ (isotropy.lift S Sn φ _) = φ,
  rw graph_like.lift_spec,
  apply isotropy.lift_spec,
  { rw le_iff at hφ ⊢,
    rintros a b f ⟨_,_,g,gS⟩,
    exact hφ gS, },
end

def lift_unique (Φ : quotient_groupoid S Sn ⥤ D) (hΦ : (of S Sn) ⋙ Φ = φ) :
  Φ = (lift S Sn φ hφ) :=
begin
  apply graph_like.lift_unique,
  apply isotropy.map_is_graph_like,
  { rw le_iff at hφ ⊢,
    rintros a b f ⟨_,_,g,gS⟩,
    exact hφ gS, },
  apply isotropy.lift_unique,
  exact hΦ,
end

end ump

lemma ker_eq : ker (of S Sn) = S :=
begin
  change ker (isotropy.of S Sn ⋙ (graph_like.of (map (isotropy.of S Sn) _ S) _)) = S,
  rw ker_comp,
  rw graph_like.ker_eq,
  apply le_antisymm,
  { rw le_iff, rintros c d f hf,
    dsimp [comap] at hf, rw mem_map_iff at hf,
    obtain ⟨c',d',g,cc',dd',gS,e⟩ := hf,
    cases isotropy.of_inj_on_objects S Sn cc',
    cases isotropy.of_inj_on_objects S Sn dd',
    simp only [eq_to_hom_refl, category.comp_id, category.id_comp] at e,
    letI := @cgr.setoid _ _ S Sn.to_is_wide c d,
    obtain ⟨γ,γS,δ,δS,e⟩ := quotient.exact e,
    have : f = inv γ ≫ g ≫ inv δ, by { rw e, simp, },
    rw this,
    apply S.mul (S.inv γS) (S.mul gS $ S.inv δS), },
  { apply subgroupoid.le_map_comap, },
  apply isotropy.map_is_graph_like,
end

end quotient

end quotient_groupoid

end category_theory