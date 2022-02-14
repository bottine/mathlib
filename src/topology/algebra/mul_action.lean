/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.algebra.monoid
import group_theory.group_action.prod
import group_theory.group_action.basic
import topology.homeomorph
import topology.algebra.const_mul_action

/-!
# Continuous monoid action

In this file we define class `has_continuous_smul`. We say `has_continuous_smul M X` if `M` acts on
`X` and the map `(c, x) ↦ c • x` is continuous on `M × X`. We reuse this class for topological
(semi)modules, vector spaces and algebras.

## Main definitions

* `has_continuous_smul M X` : typeclass saying that the map `(c, x) ↦ c • x` is continuous
  on `M × X`;
* `homeomorph.smul_of_ne_zero`: if a group with zero `G₀` (e.g., a field) acts on `X` and `c : G₀`
  is a nonzero element of `G₀`, then scalar multiplication by `c` is a homeomorphism of `X`;
* `homeomorph.smul`: scalar multiplication by an element of a group `G` acting on `X`
  is a homeomorphism of `X`.
* `units.has_continuous_smul`: scalar multiplication by `Mˣ` is continuous when scalar
  multiplication by `M` is continuous. This allows `homeomorph.smul` to be used with on monoids
  with `G = Mˣ`.

## Main results

Besides homeomorphisms mentioned above, in this file we provide lemmas like `continuous.smul`
or `filter.tendsto.smul` that provide dot-syntax access to `continuous_smul`.
-/

open_locale topological_space pointwise
open filter

/-- Class `has_continuous_smul M X` says that the scalar multiplication `(•) : M → X → X`
is continuous in both arguments. We use the same class for all kinds of multiplicative actions,
including (semi)modules and algebras. -/
class has_continuous_smul (M X : Type*) [has_scalar M X]
  [topological_space M] [topological_space X] : Prop :=
(continuous_smul : continuous (λp : M × X, p.1 • p.2))

export has_continuous_smul (continuous_smul)

/-- Class `has_continuous_vadd M X` says that the additive action `(+ᵥ) : M → X → X`
is continuous in both arguments. We use the same class for all kinds of additive actions,
including (semi)modules and algebras. -/
class has_continuous_vadd (M X : Type*) [has_vadd M X]
  [topological_space M] [topological_space X] : Prop :=
(continuous_vadd : continuous (λp : M × X, p.1 +ᵥ p.2))

export has_continuous_vadd (continuous_vadd)

attribute [to_additive] has_continuous_smul

section main

variables {M X Y α : Type*} [topological_space M] [topological_space X] [topological_space Y]

section has_scalar

variables [has_scalar M X] [has_continuous_smul M X]

@[priority 100, to_additive] instance has_continuous_smul.has_continuous_const_smul :
  has_continuous_const_smul M X :=
{ continuous_const_smul := λ _, continuous_smul.comp (continuous_const.prod_mk continuous_id) }

@[to_additive]
lemma filter.tendsto.smul {f : α → M} {g : α → X} {l : filter α} {c : M} {a : X}
  (hf : tendsto f l (𝓝 c)) (hg : tendsto g l (𝓝 a)) :
  tendsto (λ x, f x • g x) l (𝓝 $ c • a) :=
(continuous_smul.tendsto _).comp (hf.prod_mk_nhds hg)

@[to_additive]
lemma filter.tendsto.const_smul {f : α → X} {l : filter α} {a : X} (hf : tendsto f l (𝓝 a))
  (c : M) :
  tendsto (λ x, c • f x) l (𝓝 (c • a)) :=
tendsto_const_nhds.smul hf

@[to_additive]
lemma filter.tendsto.smul_const {f : α → M} {l : filter α} {c : M}
  (hf : tendsto f l (𝓝 c)) (a : X) :
  tendsto (λ x, (f x) • a) l (𝓝 (c • a)) :=
hf.smul tendsto_const_nhds

variables {f : Y → M} {g : Y → X} {b : Y} {s : set Y}

@[to_additive]
lemma continuous_within_at.smul (hf : continuous_within_at f s b)
  (hg : continuous_within_at g s b) :
  continuous_within_at (λ x, f x • g x) s b :=
hf.smul hg

@[to_additive]
lemma continuous_within_at.const_smul (hg : continuous_within_at g s b) (c : M) :
  continuous_within_at (λ x, c • g x) s b :=
hg.const_smul c

@[to_additive]
lemma continuous_at.smul (hf : continuous_at f b) (hg : continuous_at g b) :
  continuous_at (λ x, f x • g x) b :=
hf.smul hg

@[to_additive]
lemma continuous_at.const_smul (hg : continuous_at g b) (c : M) :
  continuous_at (λ x, c • g x) b :=
hg.const_smul c

@[to_additive]
lemma continuous_on.smul (hf : continuous_on f s) (hg : continuous_on g s) :
  continuous_on (λ x, f x • g x) s :=
λ x hx, (hf x hx).smul (hg x hx)

@[to_additive]
lemma continuous_on.const_smul (hg : continuous_on g s) (c : M) :
  continuous_on (λ x, c • g x) s :=
λ x hx, (hg x hx).const_smul c

@[continuity, to_additive]
lemma continuous.smul (hf : continuous f) (hg : continuous g) :
  continuous (λ x, f x • g x) :=
continuous_smul.comp (hf.prod_mk hg)

@[to_additive]
lemma continuous.const_smul (hg : continuous g) (c : M) :
  continuous (λ x, c • g x) :=
continuous_smul.comp (continuous_const.prod_mk hg)

/-- If a scalar is central, then its right action is continuous when its left action is. -/
instance has_continuous_smul.op [has_scalar Mᵐᵒᵖ X] [is_central_scalar M X] :
  has_continuous_smul Mᵐᵒᵖ X :=
⟨ suffices continuous (λ p : M × X, mul_opposite.op p.fst • p.snd),
  from this.comp (mul_opposite.continuous_unop.prod_map continuous_id),
  by simpa only [op_smul_eq_smul] using (continuous_smul : continuous (λ p : M × X, _)) ⟩

end has_scalar

section monoid

variables [monoid M] [mul_action M X] [has_continuous_smul M X]

@[to_additive] instance units.has_continuous_smul : has_continuous_smul Mˣ X :=
{ continuous_smul :=
    show continuous ((λ p : M × X, p.fst • p.snd) ∘ (λ p : Mˣ × X, (p.1, p.2))),
    from continuous_smul.comp ((units.continuous_coe.comp continuous_fst).prod_mk continuous_snd) }

@[to_additive]
lemma smul_closure_subset (c : M) (s : set X) : c • closure s ⊆ closure (c • s) :=
((set.maps_to_image _ _).closure $ continuous_id.const_smul c).image_subset

@[to_additive]
lemma smul_closure_orbit_subset (c : M) (x : X) :
  c • closure (mul_action.orbit M x) ⊆ closure (mul_action.orbit M x) :=
(smul_closure_subset c _).trans $ closure_mono $ mul_action.smul_orbit_subset _ _

end monoid

section group

variables {G : Type*} [topological_space G] [group G] [mul_action G X]
  [has_continuous_smul G X]

@[to_additive]
lemma tendsto_const_smul_iff {f : α → X} {l : filter α} {a : X} (c : G) :
  tendsto (λ x, c • f x) l (𝓝 $ c • a) ↔ tendsto f l (𝓝 a) :=
⟨λ h, by simpa only [inv_smul_smul] using h.const_smul c⁻¹,
  λ h, h.const_smul _⟩

variables {f : Y → X} {b : Y} {s : set Y}

@[to_additive]
lemma continuous_within_at_const_smul_iff (c : G) :
  continuous_within_at (λ x, c • f x) s b ↔ continuous_within_at f s b :=
tendsto_const_smul_iff c

@[to_additive]
lemma continuous_on_const_smul_iff (c : G) : continuous_on (λ x, c • f x) s ↔ continuous_on f s :=
forall₂_congr $ λ b hb, continuous_within_at_const_smul_iff c

@[to_additive]
lemma continuous_at_const_smul_iff (c : G) :
  continuous_at (λ x, c • f x) b ↔ continuous_at f b :=
tendsto_const_smul_iff c

@[to_additive]
lemma continuous_const_smul_iff (c : G) :
  continuous (λ x, c • f x) ↔ continuous f :=
by simp only [continuous_iff_continuous_at, continuous_at_const_smul_iff]

@[to_additive]
lemma is_open_map_smul (c : G) : is_open_map (λ x : X, c • x) :=
(homeomorph.smul c).is_open_map

@[to_additive] lemma is_open.smul {s : set X} (hs : is_open s) (c : G) : is_open (c • s) :=
is_open_map_smul c s hs

@[to_additive]
lemma is_closed_map_smul (c : G) : is_closed_map (λ x : X, c • x) :=
(homeomorph.smul c).is_closed_map

@[to_additive] lemma is_closed.smul {s : set X} (hs : is_closed s) (c : G) : is_closed (c • s) :=
is_closed_map_smul c s hs

end group

section group_with_zero

variables {G₀ : Type*} [topological_space G₀] [group_with_zero G₀] [mul_action G₀ X]
  [has_continuous_smul G₀ X]

lemma tendsto_const_smul_iff₀ {f : α → X} {l : filter α} {a : X} {c : G₀} (hc : c ≠ 0) :
  tendsto (λ x, c • f x) l (𝓝 $ c • a) ↔ tendsto f l (𝓝 a) :=
tendsto_const_smul_iff (units.mk0 c hc)

variables {f : Y → X} {b : Y} {c : G₀} {s : set Y}

lemma continuous_within_at_const_smul_iff₀ (hc : c ≠ 0) :
  continuous_within_at (λ x, c • f x) s b ↔ continuous_within_at f s b :=
tendsto_const_smul_iff (units.mk0 c hc)

lemma continuous_on_const_smul_iff₀ (hc : c ≠ 0) :
  continuous_on (λ x, c • f x) s ↔ continuous_on f s :=
continuous_on_const_smul_iff (units.mk0 c hc)

lemma continuous_at_const_smul_iff₀ (hc : c ≠ 0) :
  continuous_at (λ x, c • f x) b ↔ continuous_at f b :=
continuous_at_const_smul_iff (units.mk0 c hc)

lemma continuous_const_smul_iff₀ (hc : c ≠ 0) :
  continuous (λ x, c • f x) ↔ continuous f :=
continuous_const_smul_iff (units.mk0 c hc)

/-- Scalar multiplication by a non-zero element of a group with zero acting on `X` is a
homeomorphism from `X` onto itself. -/
protected def homeomorph.smul_of_ne_zero (c : G₀) (hc : c ≠ 0) : X ≃ₜ X :=
homeomorph.smul (units.mk0 c hc)

lemma is_open_map_smul₀ {c : G₀} (hc : c ≠ 0) : is_open_map (λ x : X, c • x) :=
(homeomorph.smul_of_ne_zero c hc).is_open_map

lemma is_open.smul₀ {c : G₀} {s : set X} (hs : is_open s) (hc : c ≠ 0) : is_open (c • s) :=
is_open_map_smul₀ hc s hs

lemma interior_smul₀ {c : G₀} (hc : c ≠ 0) (s : set X) : interior (c • s) = c • interior s :=
((homeomorph.smul_of_ne_zero c hc).image_interior s).symm

/-- `smul` is a closed map in the second argument.

The lemma that `smul` is a closed map in the first argument (for a normed space over a complete
normed field) is `is_closed_map_smul_left` in `analysis.normed_space.finite_dimension`. -/
lemma is_closed_map_smul_of_ne_zero {c : G₀} (hc : c ≠ 0) : is_closed_map (λ x : X, c • x) :=
(homeomorph.smul_of_ne_zero c hc).is_closed_map

/-- `smul` is a closed map in the second argument.

The lemma that `smul` is a closed map in the first argument (for a normed space over a complete
normed field) is `is_closed_map_smul_left` in `analysis.normed_space.finite_dimension`. -/
lemma is_closed_map_smul₀ {𝕜 M : Type*} [division_ring 𝕜] [add_comm_monoid M] [topological_space M]
  [t1_space M] [module 𝕜 M] [topological_space 𝕜] [has_continuous_smul 𝕜 M] (c : 𝕜) :
  is_closed_map (λ x : M, c • x) :=
begin
  rcases eq_or_ne c 0 with (rfl|hne),
  { simp only [zero_smul], exact is_closed_map_const },
  { exact (homeomorph.smul_of_ne_zero c hne).is_closed_map },
end

end group_with_zero

namespace is_unit

variables [monoid M] [mul_action M X] [has_continuous_smul M X]

lemma tendsto_const_smul_iff {f : α → X} {l : filter α} {a : X} {c : M} (hc : is_unit c) :
  tendsto (λ x, c • f x) l (𝓝 $ c • a) ↔ tendsto f l (𝓝 a) :=
let ⟨u, hu⟩ := hc in hu ▸ tendsto_const_smul_iff u

variables {f : Y → X} {b : Y} {c : M} {s : set Y}

lemma continuous_within_at_const_smul_iff (hc : is_unit c) :
  continuous_within_at (λ x, c • f x) s b ↔ continuous_within_at f s b :=
let ⟨u, hu⟩ := hc in hu ▸ continuous_within_at_const_smul_iff u

lemma continuous_on_const_smul_iff (hc : is_unit c) :
  continuous_on (λ x, c • f x) s ↔ continuous_on f s :=
let ⟨u, hu⟩ := hc in hu ▸ continuous_on_const_smul_iff u

lemma continuous_at_const_smul_iff (hc : is_unit c) :
  continuous_at (λ x, c • f x) b ↔ continuous_at f b :=
let ⟨u, hu⟩ := hc in hu ▸ continuous_at_const_smul_iff u

lemma continuous_const_smul_iff (hc : is_unit c) :
  continuous (λ x, c • f x) ↔ continuous f :=
let ⟨u, hu⟩ := hc in hu ▸ continuous_const_smul_iff u

lemma is_open_map_smul (hc : is_unit c) : is_open_map (λ x : X, c • x) :=
let ⟨u, hu⟩ := hc in hu ▸ is_open_map_smul u

lemma is_closed_map_smul (hc : is_unit c) : is_closed_map (λ x : X, c • x) :=
let ⟨u, hu⟩ := hc in hu ▸ is_closed_map_smul u

end is_unit

@[to_additive]
instance has_continuous_mul.has_continuous_smul {M : Type*} [monoid M]
  [topological_space M] [has_continuous_mul M] :
  has_continuous_smul M M :=
⟨continuous_mul⟩

@[to_additive]
instance [has_scalar M X] [has_scalar M Y] [has_continuous_smul M X]
  [has_continuous_smul M Y] :
  has_continuous_smul M (X × Y) :=
⟨(continuous_fst.smul (continuous_fst.comp continuous_snd)).prod_mk
  (continuous_fst.smul (continuous_snd.comp continuous_snd))⟩

@[to_additive]
instance {ι : Type*} {γ : ι → Type*}
  [∀ i, topological_space (γ i)] [Π i, has_scalar M (γ i)] [∀ i, has_continuous_smul M (γ i)] :
  has_continuous_smul M (Π i, γ i) :=
⟨continuous_pi $ λ i,
  (continuous_fst.smul continuous_snd).comp $
    continuous_fst.prod_mk ((continuous_apply i).comp continuous_snd)⟩

end main

section lattice_ops

variables {ι : Sort*} {M X : Type*} [topological_space M] [has_scalar M X]

@[to_additive] lemma has_continuous_smul_Inf {ts : set (topological_space X)}
  (h : Π t ∈ ts, @has_continuous_smul M X _ _ t) :
  @has_continuous_smul M X _ _ (Inf ts) :=
{ continuous_smul :=
  begin
    rw ← @Inf_singleton _ _ ‹topological_space M›,
    exact continuous_Inf_rng (λ t ht, continuous_Inf_dom₂ (eq.refl _) ht
      (@has_continuous_smul.continuous_smul _ _ _ _ t (h t ht)))
  end }

@[to_additive] lemma has_continuous_smul_infi {ts' : ι → topological_space X}
  (h : Π i, @has_continuous_smul M X _ _ (ts' i)) :
  @has_continuous_smul M X _ _ (⨅ i, ts' i) :=
has_continuous_smul_Inf $ set.forall_range_iff.mpr h

@[to_additive] lemma has_continuous_smul_inf {t₁ t₂ : topological_space X}
  [@has_continuous_smul M X _ _ t₁] [@has_continuous_smul M X _ _ t₂] :
  @has_continuous_smul M X _ _ (t₁ ⊓ t₂) :=
by { rw inf_eq_infi, refine has_continuous_smul_infi (λ b, _), cases b; assumption }

end lattice_ops
