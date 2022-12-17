/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import category_theory.filtered
import topology.category.Top.limits
import data.finset.basic
import category_theory.category.basic
import category_theory.full_subcategory
import data.set.finite
import data.fintype.basic
import category_theory.types

/-!
# Mittag Leffler

This files defines the Mittag-Leffler condition for cofiltered systems and (TODO) other properties
of such systems and their sections.

## Main definitions

Given the functor `F : J ⥤ Type v`:

* For `j : J`, `F.eventual_range j` is the intersections of all ranges of morphisms `F.map f`
  where `f` has codomain `j`.
* `is_mittag_leffler` states that the functor `F : J → Type v`, satisfies the Mittag-Leffler
  condition: the ranges of morphisms `F.map f` (with `f` having codomain `j`) stabilize.
* If `J` is cofiltered `F.to_eventual_ranges` is the subfunctor of `F` obtained by restriction
  to `F.eventual_range`.


## Main statements

* `is_mittag_leffler_of_exists_finite_range` shows that if `J` is cofiltered and for all `j`,
  there exists some `i` and `f : i ⟶ j` such that the range of `F.map f` is finite, then
  `F` is Mittag-Leffler.
* `to_eventual_ranges_surjective` shows that if `F` is Mittag-Leffler, then `F.to_eventual_ranges`
  has all morphisms `F.map f` surjective.

## Todo

* Specialize to inverse systems and fintype systems.
* Prove [Stacks: Lemma 0597](https://stacks.math.columbia.edu/tag/0597)

## References

* [Stacks: Mittag-Leffler systems](https://stacks.math.columbia.edu/tag/0594)

## Tags

Mittag-Leffler, surjective, eventual range, inverse system,

-/


universes u v w

namespace category_theory
namespace functor

/--
The eventual range of the functor `F : J ⥤ Type v` at index `j : J` is the intersection
of the ranges of all maps `F.map f` with `i : J` and `f : i ⟶ j`.
-/
def eventual_range
  {J : Type u} [category J] (F : J ⥤ Type v) (j : J) :=
⋂ (i : J) (f : i ⟶ j), set.range (F.map f)

/--
The functor `F : J ⥤ Type v` satisfies the Mittag-Leffler condition if for all `j : J`,
there exists some `i : J` and `f : i ⟶ j` such that for all `k : J` and `g : k ⟶ j`, the range
of `F.map f` is contained in that of `F.map g`;
in other words (see `is_mittag_leffler_iff_eventual_range`), the eventual range at `j` is attained
by some `f : i ⟶ j`.
-/
def is_mittag_leffler
  {J : Type u} [category J] (F : J ⥤ Type v) :=
∀ (j : J), ∃ (i) (f : i ⟶ j), ∀ (k) (g : k ⟶ j), set.range (F.map f) ⊆ set.range (F.map g)

lemma is_mittag_leffler_iff_eventual_range
  {J : Type u} [category J] (F : J ⥤ Type v) :
  F.is_mittag_leffler ↔ ∀ (j : J), ∃ (i) (f : i ⟶ j), F.eventual_range j = set.range (F.map f) :=
begin
  refine forall_congr (λ j, exists_congr $ λ i, exists_congr $ λ f, _),
  split,
  { rintro h, apply subset_antisymm,
    { apply set.Inter₂_subset, },
    { apply set.subset_Inter₂,
      exact λ k g, h k g, }, },
  { rintro h k g, rw h.symm,
    apply set.Inter₂_subset, },
end

lemma eventual_range_eq_range_precomp
  {J : Type u} [category J] (F : J ⥤ Type v)
  {i j k : J} (f : i ⟶ j) (g : j ⟶ k) (h : F.eventual_range k = set.range (F.map g)) :
  F.eventual_range k = (set.range (F.map $ f ≫ g)) :=
begin
  apply subset_antisymm,
  { apply set.Inter₂_subset, },
  { simp only [h, types_comp, functor.map_comp], apply set.range_comp_subset_range, }
end

lemma is_mittag_leffler_of_surjective
  {J : Type u} [category J] (F : J ⥤ Type v) :
  (∀ (i j : J) (f : i ⟶ j), (F.map f).surjective) → F.is_mittag_leffler :=
begin
  refine λ h j, ⟨j, 𝟙 j, λ k g, subset_of_eq _⟩,
  simp only [map_id, types_id, set.range_id],
  exact (set.range_iff_surjective.mpr $ h k j g).symm,
end

/--
TODO: where does this go?
-/
lemma _root_.category_theory.is_cofiltered.cone_over_cospan
  {J : Type u} [category J] [is_cofiltered J] {i j j' : J} (f : j ⟶ i) (f' : j' ⟶ i)  :
  ∃ (k : J) (g : k ⟶ j) (g' : k ⟶ j'), g ≫ f = g' ≫ f' :=
begin
  let h := is_cofiltered.min_to_left j j',
  let h' := is_cofiltered.min_to_right j j',
  let G := is_cofiltered.eq_hom (h ≫ f) (h' ≫ f'),
  refine ⟨_, G ≫ h, G ≫ h', _⟩,
  simp only [category.assoc, is_cofiltered.eq_condition],
end

lemma ranges_directed_of_is_cofiltered
  {J : Type u} [category J] [is_cofiltered J] (F : J ⥤ Type v) (j : J) :
  directed_on (⊇) (set.range (λ ( f : Σ' (i : J), i ⟶ j), set.range (F.map f.2))) :=
begin
  rintros _ ⟨⟨i, ij⟩, rfl⟩ _ ⟨⟨k, kj⟩, rfl⟩,
  obtain ⟨l, li, lk, e⟩ := category_theory.is_cofiltered.cone_over_cospan ij kj,
  refine ⟨set.range (F.map $ li ≫ ij), _⟩,
  rw [set.mem_range, exists_prop],
  refine ⟨⟨⟨l, li ≫ ij⟩, rfl⟩, ⟨_, _⟩⟩,
  rotate, rw e,
  all_goals
  { simp_rw [functor.map_comp, types_comp],
    apply set.range_comp_subset_range, },
end

/--
TODO: where does this go?
-/
private lemma directed_on_min {J : Type u} {s : set J} [preorder J] (h : directed_on (≥) s)
  (m ∈ s) (min : ∀ (a ∈ s), a ≤ m → a = m) : ∀ a ∈ s, m ≤ a :=
λ a as, let ⟨x, xs, xm, xa⟩ := h m H a as in (min x xs xm) ▸ xa

lemma is_mittag_leffler_of_exists_finite_range
  {J : Type u} [category.{w} J] [is_cofiltered J] (F : J ⥤ Type v)
  (h : ∀ (j : J), ∃ i (f : i ⟶ j), (set.range (F.map f)).finite ) :
  F.is_mittag_leffler :=
begin
  rintro j,
  suffices : ∃ (f : Σ' i, i ⟶ j), ∀ (f' : Σ' i, i ⟶ j),
               set.range (F.map f'.2) ≤ set.range (F.map f.2) →
                 set.range (F.map f'.2) = set.range (F.map f.2),
  { obtain ⟨⟨i, f⟩, fmin⟩ := this,
    refine ⟨i, f, λ i' f', _⟩,
    refine directed_on_min (F.ranges_directed_of_is_cofiltered j) _ ⟨⟨i, f⟩, rfl⟩ _ _ ⟨⟨i', f'⟩, rfl⟩,
    simp only [set.mem_range, psigma.exists, forall_exists_index],
    rintro _ k g rfl gf,
    exact fmin ⟨k, g⟩ gf, },

  let fins := subtype { f : Σ' i, i ⟶ j | (set.range (F.map f.2)).finite },
  haveI : nonempty fins := by { obtain ⟨i, f, fin⟩ := h j, exact ⟨⟨⟨i, f⟩, fin⟩⟩, },
  let fmin := function.argmin (λ (f : fins), f.prop.to_finset.card) nat.lt_wf,
  use fmin.val,
  rintro g gf,
  cases lt_or_eq_of_le gf,
  { have gfin : (set.range (F.map g.2)).finite := fmin.prop.subset gf,
    refine ((λ (f : fins), f.prop.to_finset.card).not_lt_argmin nat.lt_wf ⟨g, gfin⟩ _).elim,
    exact finset.card_lt_card (set.finite.to_finset_ssubset.mpr h_1), },
  { assumption, },
end

/--
The subfunctor of `F` obtained by restricting to the eventual range at each index.
-/
def to_eventual_ranges
  {J : Type u} [category J] [is_cofiltered J] (F : J ⥤ Type v) : J ⥤ Type v :=
{ obj := λ j, F.eventual_range j,
  map := λ i j f, set.maps_to.restrict (F.map f) _ _ ( by
    { rintro x h,
      simp only [eventual_range, set.mem_Inter, set.mem_range] at h ⊢,
      rintro i' f',
      obtain ⟨l, g, g', e⟩ := category_theory.is_cofiltered.cone_over_cospan f f',
      obtain ⟨z, rfl⟩ := h l g,
      use F.map g' z,
      replace e := congr_fun (congr_arg F.map e) z,
      simp_rw functor_to_types.map_comp_apply at e,
      exact e.symm, } ),
  map_id' := by
    { rintros, ext,
      simp only [set.maps_to.coe_restrict_apply, types_id_apply, map_id], },
  map_comp' := by
    { intros, ext,
      simp only [functor.map_comp, set.maps_to.coe_restrict_apply, types_comp_apply], }, }

/--
The sections of the functor `F : J ⥤ Type v` are in bijection with the sections of
`F.eventual_ranges`.
-/
def to_eventual_ranges_sections_equiv
  {J : Type u} [category J] [is_cofiltered J] (F : J ⥤ Type v) :
  F.to_eventual_ranges.sections ≃ F.sections :=
{ to_fun := λ ss,
    ⟨ λ j, (ss.val j).val,
      λ i j f, by simpa only [←subtype.coe_inj, subtype.coe_mk] using ss.prop f ⟩,
  inv_fun := λ s,
    ⟨ λ j,
      ⟨ s.val j, by
        { dsimp [eventual_range],
          simp only [set.mem_Inter, set.mem_range],
          exact λ i f, ⟨s.val i, s.prop f⟩, } ⟩,
      λ i j ij, subtype.mk_eq_mk.mpr (s.prop ij)⟩,
  left_inv := by
    { simp only [function.right_inverse, function.left_inverse, subtype.val_eq_coe, set_coe.forall,
                 subtype.coe_mk, subtype.coe_eta, eq_self_iff_true, implies_true_iff], },
  right_inv := by
    { simp only [function.left_inverse, function.right_inverse, eq_self_iff_true, set_coe.forall,
                 implies_true_iff, subtype.coe_mk], } }

/--
If `F` satisfies the Mittag-Leffler condition, its restriction to eventual ranges is a surjective
functor.
-/
lemma to_eventual_ranges_surjective
  {J : Type u} [category J] [is_cofiltered J] (F : J ⥤ Type v) (ml : F.is_mittag_leffler) :
  ∀ (i j : J) (f : i ⟶ j), (F.to_eventual_ranges.map f).surjective :=
begin
  rintros i j f ⟨x, hx⟩,
  rw is_mittag_leffler_iff_eventual_range at ml,
  dsimp only [to_eventual_ranges],
  simp only [set_coe.exists],
  obtain ⟨i₀, ii₀, ei₀⟩ := ml i,
  obtain ⟨j₀, jj₀, ej₀⟩ := ml j,
  obtain ⟨k, ki₀, kj₀, e⟩ := category_theory.is_cofiltered.cone_over_cospan (ii₀ ≫ f) jj₀,
  let ei := F.eventual_range_eq_range_precomp ki₀ ii₀ ei₀,
  let ej := F.eventual_range_eq_range_precomp kj₀ jj₀ ej₀,
  obtain ⟨z, rfl⟩ := ej.rec_on hx,
  use F.map (ki₀ ≫ ii₀) z,
  simp_rw [ei, set.mem_range_self, exists_true_left, ←e, functor_to_types.map_comp_apply],
  refl,
end

/-- If `F` has all arrows surjective, then it "factors through a poset". -/
lemma thin_diagram_of_surjective
  {J : Type u} [category J] [is_cofiltered J] (F : J ⥤ Type v)
  (Fsur : ∀ (i j : J) (f : i ⟶ j), (F.map f).surjective) :
  ∀ i j (f g : i ⟶ j), F.map f = F.map g :=
begin
  rintro i j f g,
  let φ := is_cofiltered.eq_hom f g,
  suffices : F.map φ ≫ F.map f = F.map φ ≫ F.map g,
  { let φs := Fsur _ _ φ,
    rw ←category_theory.epi_iff_surjective at φs,
    exact φs.left_cancellation _ _ this, },
  simp_rw [←map_comp, is_cofiltered.eq_condition],
end

/-- If `F` is nonempty at each index and Mittag-Leffler, then so is `F.to_eventual_ranges`. -/
instance to_eventual_ranges_nonempty
  {J : Type u} [category J] [is_cofiltered J] (F : J ⥤ Type v) (ml : F.is_mittag_leffler)
  [∀ (j : J), nonempty (F.obj j)] : ∀ (j : J), nonempty (F.to_eventual_ranges.obj j) :=
begin
  intro j, rw is_mittag_leffler_iff_eventual_range at ml,
  obtain ⟨i,f,h⟩ := ml j,
  dsimp [to_eventual_ranges], rw h,
  apply set.nonempty.to_subtype,
  apply set.range_nonempty,
end

section sections_of_surjective
/--
Start with a surjective finite nonempty cofiltered system `F : J ⥤ Type v`.
The assumption of surjectivity is cheap in that one can take `eventual_image` anyway, which preserve
both nonempty and finite.

Fix `j₀ : J` and `x₀ : F.obj j₀`.
The goal is to exhibit a section `s : F.sections` satisfying `s j₀ = x₀`.

-/

variables
  {J : Type u} [category J] [is_cofiltered J] (F : J ⥤ Type v) [∀ (j : J), finite (F.obj j)]
  {j₀ : J} (x₀ : F.obj j₀)

include j₀ x₀

/-- The set of surjective subfunctors of F with `x₀` below -/
structure sub :=
  (obj : Π j, set (F.obj j))
  (sur_sub : ∀ i j (f : i ⟶ j), set.image (F.map f) (obj i) = obj j)
  (above : ∀ i (f : i ⟶ j₀), ∃ x ∈ obj i, (F.map f) x = x₀)

def sub_le (S T : F.sub x₀) : Prop := ∀ (j : J), S.obj j ⊆ T.obj j

@[ext] lemma sub_ext {S T : F.sub x₀} (h : ∀ j, S.obj j = T.obj j) : S = T :=
by { cases S, cases T, simp only at h ⊢, ext j x, rw h j, }

/-- Careful: we invert the order to make using Zorn that bit easier. -/
instance : partial_order (F.sub x₀) :=
begin
  fconstructor,
  { exact λ S T, sub_le F x₀ T S, },
  { exact λ S j, subset_refl (S.obj j), },
  { exact λ R S T RS ST j, subset_trans (ST j) (RS j), },
  { exact λ S T ST TS, sub_ext F x₀ (λj,subset_antisymm (TS j) (ST j)), },
end

/--
The intersection of a nonempty chain of surjective subfunctors above `x₀`
is also a subfunctor above `x₀`.
-/
def chain_Inter  : ∀ (c : set $ F.sub x₀), is_chain (F.sub_le x₀) c → c.nonempty → F.sub x₀ :=
begin
  rintro c cchain cnempty,
  have mmin : ∀ j, ∃ (S : c), ∀ (T : c), S.val.obj j ⊆ T.val.obj j, by
  { rintro j,
    let mcard : F.sub x₀ → ℕ := by
    { rintro S,
      have : (S.obj j).finite, by
      { apply set.finite.subset,
        apply set.finite_univ,
        simp only [set.subset_univ], },
      exact this.to_finset.card, },
    let S := function.argmin_on mcard nat.lt_wf c cnempty,
    let Sc :=mcard.argmin_on_mem nat.lt_wf c cnempty,
    use ⟨S,Sc⟩,
    rintro ⟨T,Tc⟩,
    by_cases SeqT : S = T,
    { induction SeqT, refl, },
    { specialize cchain Sc Tc SeqT,
      cases cchain,
      { exact cchain j, },
      { by_contra',
        apply function.not_lt_argmin_on mcard nat.lt_wf c Tc,
        apply finset.card_lt_card,
        rw set.finite.to_finset_ssubset,
        exact ssubset_iff_subset_not_subset.mpr ⟨cchain j,this⟩, }, }, },
  refine ⟨λ j, ⋂ (S : c), S.val.obj j,_,_⟩,
  { rintro i j f,
    obtain ⟨Si,Simin⟩ := mmin i,
    have : (⋂ (S : c), S.val.obj i) = Si.val.obj i, by
    { refine subset_antisymm (set.Inter_subset _ _) (set.subset_Inter Simin), },
    rw this,
    apply subset_antisymm,
    apply set.subset_Inter,
    { rintro S, rw ←S.val.sur_sub _ _ f,
      apply set.image_subset, apply Simin, },
    { rw Si.val.sur_sub _ _ f,
      apply set.Inter_subset, }, },
  { rintro i f,
    obtain ⟨Si,Simin⟩ := mmin i,
    have : (⋂ (S : c), S.val.obj i) = Si.val.obj i, by
    { refine subset_antisymm (set.Inter_subset _ _) (set.subset_Inter Simin), },
    rw this,
    apply Si.val.above, },
end

/-- The intersection is contained in any subfunctor in the chain. -/
lemma chain_Inter_le
  (c : set $ F.sub x₀) (cchain : is_chain (F.sub_le x₀) c) (cnempty : c.nonempty)
  (S : F.sub x₀) ( Sc : S ∈ c) : F.sub_le x₀ (chain_Inter F x₀ c cchain cnempty) S :=
begin
  simp [upper_bounds, chain_Inter], rintro j, apply set.Inter₂_subset, exact Sc,
end

variables (Fs : ∀ (i j : J) (f : i ⟶ j), (F.map f).surjective)
include Fs

def sub_univ : F.sub x₀ :=
{ obj := λ j, set.univ,
  sur_sub := λ i j f, by
  { simp only [set.image_univ], rw set.range_iff_surjective, apply Fs, },
  above := λ i f, by
  { simp only [set.mem_univ, exists_true_left], apply Fs, } }

instance : nonempty (F.sub x₀) := ⟨F.sub_univ x₀ Fs⟩

/--
Given a subfunctor and a point `x` in the section, with `x` mapping to `x₀`
this is the best approximation to the restriction to elements mapping to `x`.
-/
def restrict (S : F.sub x₀) {j₁ : J} {x₁ : F.obj j₁}
  (x₁₀ : ∃ f : j₁ ⟶ j₀, F.map f x₁ = x₀) (x₁S : x₁ ∈ S.obj j₁) : F.sub x₀ :=
{ obj := λ i,
  { y | y ∈ S.obj i ∧ ∃ (k : J) (g : k ⟶ j₁) (h : k ⟶ i),
                      ∃ (z : F.obj k), z ∈ S.obj k ∧ F.map g z = x₁ ∧ F.map h z = y },
  sur_sub := λ i i' f, by
  { ext y, split,
    { rintro ⟨z,⟨zS,zH⟩,rfl⟩,
      simp only [←S.sur_sub _ _ f, set.mem_image, set.mem_set_of_eq],
      use [z,zS],
      obtain ⟨k,g,h,z',z'S,rfl,rfl⟩ := zH,
      use [k,g,h≫f,z',z'S,rfl],
      rw [←functor_to_types.map_comp_apply], },
    { rintro ⟨yS,⟨k,g,h,z,zS,rfl,rfl⟩⟩,
      let k' := is_cofiltered.min i k,
      let k'k := is_cofiltered.min_to_right i k,
      let k'i := is_cofiltered.min_to_left i k,
      rw ←S.sur_sub _ _ k'k at zS,
      obtain ⟨z',z'S,rfl⟩ := zS,
      simp only [set.mem_image, set.mem_set_of_eq, ←S.sur_sub _ _ k'i],
      use [F.map k'i z', z',z'S,k', k'k ≫ g, k'i, z', z'S],
      { simp, },
      { simp_rw [←functor_to_types.map_comp_apply],
        apply congr_fun,
        apply thin_diagram_of_surjective F Fs, } } },
  above := λ i f, by
  { obtain ⟨j₁₀,rfl⟩ := x₁₀,
    let k := is_cofiltered.min i j₁,
    let h := is_cofiltered.min_to_left i j₁,
    let g := is_cofiltered.min_to_right i j₁,
    rw ←S.sur_sub _ _ g at x₁S,
    obtain ⟨z,zS,rfl⟩ := x₁S,
    simp only [set.mem_set_of_eq, ←S.sur_sub _ _ h, set.mem_image],
    use [F.map h z, z, zS, k, g, h, z, zS, rfl, rfl],
    simp_rw [←functor_to_types.map_comp_apply],
    apply congr_fun _ z,
    apply thin_diagram_of_surjective F Fs, } }

/-- The restriction, at index `j₁`, contains only `x₁`. -/
lemma restrict_at (S : F.sub x₀) {j₁ : J} {x₁ : F.obj j₁}
  (x₁₀ : ∃ f : j₁ ⟶ j₀, F.map f x₁ = x₀) (x₁S : x₁ ∈ S.obj j₁) :
  (F.restrict x₀ Fs S x₁₀ x₁S).obj j₁ = {x₁} :=
begin
  ext y, split,
  { rintro ⟨yS,k,g,h,z,zS,rfl,rfl⟩,
    simp only [set.mem_singleton_iff],
    apply congr_fun, apply thin_diagram_of_surjective F Fs, },
  { simp only [set.mem_singleton_iff, set.mem_set_of_eq],
    rintro rfl,
    use [x₁S, j₁, 𝟙 j₁, 𝟙 j₁],
    simp only [functor_to_types.map_id_apply, and_self, exists_eq_right],
    exact x₁S, }
end

lemma restrict_le (S : F.sub x₀) {j₁ : J} {x₁ : F.obj j₁}
  (x₁₀ : ∃ f : j₁ ⟶ j₀, F.map f x₁ = x₀) (x₁S : x₁ ∈ S.obj j₁) :
  F.sub_le x₀ (F.restrict x₀ Fs S x₁₀ x₁S) S := λ j x h, h.1

lemma restrict_ne (S : F.sub x₀) {j₁ : J} {x₁ : F.obj j₁}
  (x₁₀ : ∃ f : j₁ ⟶ j₀, F.map f x₁ = x₀) (x₁S : x₁ ∈ S.obj j₁)
  (hne : ∃ y₁ : F.obj j₁, y₁ ∈ S.obj j₁ ∧ y₁ ≠ x₁) : (F.restrict x₀ Fs S x₁₀ x₁S) ≠ S :=
begin
  rintro e,
  obtain ⟨y,yS,yne⟩ := hne,
  apply yne,
  let := F.restrict_at x₀ Fs S x₁₀ x₁S,
  rw e at this,
  rw this at yS,
  exact yS,
end

lemma singletons_of_min (S : F.sub x₀) (Smin : ∀ T, S ≤ T → T = S) : ∀ j, ∃ x, S.obj j = {x} :=
begin
  by_contra' notsing,
  obtain ⟨j,jnotsing⟩ := notsing,
  let j₁ := is_cofiltered.min j j₀,
  let h := is_cofiltered.min_to_left j j₀,
  let g := is_cofiltered.min_to_right j j₀,
  have : ∀ x, x ∈ S.obj j₁ → ∃ y, y ∈ S.obj j₁ ∧ y ≠ x, by
  { rintro x xS, by_contra',
    apply jnotsing (F.map h x),
    rw ←S.sur_sub _ _ h,
    ext y, split,
    { rintro ⟨z,zS,rfl⟩, simp [this z zS], },
    { simp only [set.mem_singleton_iff, set.mem_image], rintro rfl, refine ⟨x,xS,rfl⟩,
       } },
  obtain ⟨x₁,x₁S,rfl⟩ := S.above _ g,
  let T := F.restrict _ Fs S ⟨g,rfl⟩ x₁S,
  apply F.restrict_ne _ Fs S ⟨g,rfl⟩,
  exact this x₁ x₁S,
  apply Smin,
  apply F.restrict_le _ Fs S ⟨g,rfl⟩,
  exact x₁S,
end

lemma exists_section_of_singletons (S : F.sub x₀) (hS : ∀ j, ∃ x, S.obj j = {x}) :
  ∃ s : F.sections, s.val j₀ = x₀ :=
⟨ ⟨ λ j, (hS j).some, by
    { rintro j j' f,
      apply set.eq_of_mem_singleton,
      rw [←(hS j').some_spec, ←(S.sur_sub _ _ f)],
      refine ⟨(hS j).some, _, rfl⟩,
      convert set.mem_singleton (hS j).some,
      exact (hS j).some_spec, } ⟩,
  by { obtain ⟨x,e⟩ := hS j₀,
       obtain ⟨x₁,x₁S,h⟩ := S.above j₀ (𝟙 j₀),
       let := (hS j₀).some_spec,
       simp only [*, set.singleton_eq_singleton_iff, functor_to_types.map_id_apply,
                  set.mem_singleton_iff] at *, subst_vars,
       exact this.symm, }
     ⟩

lemma exists_section : ∃ s : F.sections, s.val j₀ = x₀ :=
begin
  suffices : ∃ (S : F.sub x₀), ∀ (T : F.sub x₀), S ≤ T → T = S,
  { obtain ⟨S,Smin⟩ := this,
    apply F.exists_section_of_singletons x₀ Fs S,
    apply F.singletons_of_min x₀ Fs S Smin, },
  haveI : nonempty (F.sub x₀) := ⟨F.sub_univ x₀ Fs⟩,
  apply @zorn_nonempty_partial_order (F.sub x₀),
  rintro c cchain cnempty,
  refine ⟨F.chain_Inter x₀ c _ cnempty, F.chain_Inter_le x₀ c _ cnempty⟩,
  { simp only [is_chain] at cchain ⊢, convert cchain, funext, apply propext, tauto, },
end

end sections_of_surjective

end functor
end category_theory
