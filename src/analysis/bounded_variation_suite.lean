/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.measure.lebesgue
import analysis.calculus.monotone
import analysis.bounded_variation
import tactic.swap_var
import data.real.ereal

open_locale big_operators nnreal ennreal
open set measure_theory



section preliminaries

/--
Only really need `[total_on (≤) β]` and probably `[antisymm_on (≤) α]` but who cares.
-/
lemma monotone_on_of_right_inv_on_of_maps_to_of_monotone
  {α β : Type*} [partial_order α] [linear_order β] {φ : β → α} {ψ : α → β}
  {t : set β} {s : set α} (φψs : right_inv_on ψ φ s) (ψts : maps_to ψ s t)
  (hφ : monotone_on φ t) : monotone_on ψ s :=
begin
  rintro x xs y ys l,
  rcases le_total (ψ x) (ψ y) with (ψxy|ψyx),
  { exact ψxy, },
  { cases le_antisymm l (φψs.eq ys ▸ φψs.eq xs ▸ hφ (ψts ys) (ψts xs) ψyx), refl, },
end

end preliminaries

namespace evariation_on

variables {α β : Type*} [linear_order α] [linear_order β]
{E F : Type*} [pseudo_emetric_space E] [pseudo_emetric_space F]
{V : Type*} [normed_add_comm_group V] [normed_space ℝ V] [finite_dimensional ℝ V]

lemma comp_mono (f : α → E) {s : set α} {t : set β} (φ : β → α)
  (hφ : monotone_on φ t ) (φst : set.maps_to φ t s) :
  evariation_on (f∘φ) t ≤ evariation_on f s :=
begin
  apply supr_le _,
  rintros ⟨n, ⟨u, hu, ut⟩⟩,
  exact le_supr (λ (p : ℕ × {u : ℕ → α // monotone u ∧ ∀ i, u i ∈ s}),
    ∑ i in finset.range p.1, edist (f ((p.2 : ℕ → α) (i+1))) (f ((p.2 : ℕ → α) i)))
    ⟨n, ⟨φ ∘ u, λ x y xy, hφ (ut x) (ut y) (hu xy), λ i, φst (ut i)⟩⟩,
end

lemma eq_of_eq_on {f f' : α → E} {s : set α} (h : set.eq_on f f' s) :
  evariation_on f s = evariation_on f' s :=
begin
  dsimp only [evariation_on],
  congr' 1 with p : 1,
  congr' 1 with i : 1,
  congr' 1;
  exact h (p.2.2.2 _),
end

lemma comp_eq (f : α → E) {s : set α} {t : set β} [nonempty β] (φ : β → α)
  (hφ : monotone_on φ t ) (φst : set.maps_to φ t s) (φsur : set.surj_on φ t s) :
  evariation_on (f∘φ) t = evariation_on f s :=
begin
  apply le_antisymm (comp_mono f φ hφ φst),

  let ψ := φ.inv_fun_on t,
  have ψφs : set.eq_on (φ∘ψ) id s := φsur.right_inv_on_inv_fun_on,
  have ψts : set.maps_to ψ s t := φsur.maps_to_inv_fun_on,
  have hψ : monotone_on ψ s := monotone_on_of_right_inv_on_of_maps_to_of_monotone ψφs ψts hφ,

  change evariation_on (f∘id) s ≤ evariation_on (f ∘ φ) t,
  rw ←eq_of_eq_on (ψφs.comp_left : set.eq_on (f ∘ (φ∘ψ)) (f ∘ id) s),
  apply comp_mono _ ψ hψ ψts,
end

end evariation_on


section unit_param
/--
Fix:

* An interval `I : set ℝ`
-/

variables {E : Type*} [pseudo_emetric_space E]
variables {I : set ℝ} (f : I → E)
          (hI : ∀ (a b c : ℝ), a ≤ c → c ≤ b → a ∈ I → b ∈ I → c ∈ I)
variables (x₀ : I)
variables (hf : ∀ x : I, has_bounded_variation_on f (set.interval x₀ x))

/--
Fixing a basepoint `x₀ : ℝ`, the function `ℝ → [-∞,∞]` sending `x` to the signed variation
of `f` restricted to `[x₀,x]`, resp. `[x,x₀]`, depending on sign.
  -/
noncomputable def arc_length (x : ℝ) : ereal :=
if x₀ ≤ x then
  evariation_on f {y : I | ↑y ∈ Icc x₀ x}
else
  - evariation_on f {y : I | ↑y ∈ Icc x x₀}

-- Very sad : ↓
lemma ennreal.neg_to_ereal_le_to_ereal (a b : ennreal) : (- a : ereal) ≤ (b : ereal) :=
le_trans (by { rw [ereal.neg_le, neg_zero], positivity }) (by positivity)

lemma arc_length_monotone : monotone (arc_length f x₀) :=
begin
  rintro x₁ x₂ h,
  dsimp [arc_length],
  split_ifs,
  { rw ereal.coe_ennreal_le_coe_ennreal_iff,
    apply evariation_on.mono,
    exact λ ⟨y,hy⟩ ⟨x₀y,yx₁⟩, ⟨x₀y, yx₁.trans h⟩, },
  { exact (h_2 (h_1.trans h)).elim, },
  { apply ennreal.neg_to_ereal_le_to_ereal, },
  { rw [ereal.neg_le_neg_iff, ereal.coe_ennreal_le_coe_ennreal_iff],
    apply evariation_on.mono,
    exact λ ⟨y,hy⟩ ⟨x₂y,yx₀⟩, ⟨h.trans x₂y, yx₀⟩, }
end

/--
`f` has unit speed if its variation on any interval is the length of the interval
-/
def has_unit_speed :=
  ∀ (x y : ℝ), x ≤ y → Icc x y ⊆ I → ↑(nndist x y) = evariation_on f {z : I | z.val ∈ Icc x y}

noncomputable def unit_param :
 {y : ℝ // ∃ x : I, ↑y = arc_length f x₀ x} → E :=
λ yy, f ⟨yy.prop.some, by { obtain ⟨y,h⟩ := yy, simp only [subtype.coe_prop], }⟩ -- TODO: clean this

lemma lol (x₁ x₂ : ℝ)
  (h : evariation_on f {z : I | z.val ∈ interval x₀ x₁} =
       evariation_on f {z : I | z.val ∈ interval x₀ x₂}) : edist (f x₁) (f x₂) = 0 :=
begin

end

lemma unit_param_is_parameterization (x : I)
  (h : has_bounded_variation_on f {y | y.val ∈ set.interval x₀ x})  :
  (unit_param f x₀) ⟨(arc_length f x₀ x).to_real,sorry⟩ = f x :=
begin
  obtain ⟨x,xI⟩ := x,
  dsimp only [unit_param, arc_length],
end


example {x y : ℝ} (xy : x ≤ y) (xyI : Icc x y ⊆ I)
  (bounded_evar : evariation_on f {z : I | z.val ∈ Icc x y} < ∞) :
  ↑(nndist x y) = evariation_on (unit_param f x₀) {z | z.val ∈ Icc x y} :=
begin
  dsimp [arc_length, unit_param],
  simp,
end
/-
lemma unit_param_has_unit_speed [bvf : has_bounded_variation f]:
  has_unit_speed $ unit_param f x₀ :=
begin
  rintro x₁ x₂ l h,
  dsimp [unit_param],
  have : edist x₁ x₂ = x₂ - x₁, by library_search [h],
end
-/
end unit_param
