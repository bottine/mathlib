/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import analysis.bounded_variation
import topology.metric_space.emetric_space
import topology.path_connected
import data.real.ennreal

noncomputable theory
set_option profiler true

lemma half_nonneg {α : Type*} [linear_ordered_semifield α] {a : α} (h : 0 ≤ a) :
  0 ≤ a / 2 :=
begin
  by_contra',
  replace this := mul_lt_mul_of_pos_right this (zero_lt_two),
  simp only [div_mul_cancel, ne.def, bit0_eq_zero, one_ne_zero, not_false_iff, zero_mul] at this,
  exact (this.not_le h).elim,
end

namespace unit_interval

/-- The midpoint of the unit interval -/
abbreviation half : unit_interval := ⟨1/2, div_mem zero_le_one zero_le_two one_le_two ⟩

@[simp] lemma symm_half : symm half = half :=
subtype.ext $ sub_half 1

@[simp] lemma symm_inv : symm.involutive := symm_symm
@[simp] lemma symm_inj : symm.injective := symm_inv.injective
@[simp] lemma symm_surj : symm.surjective := symm_inv.surjective
@[simp] lemma symm_anti : antitone symm := λ x y h, (sub_le_sub_iff_left 1).mpr h


@[simp] lemma Icc_zero_one : set.Icc (0 : unit_interval) (1 : unit_interval) = set.univ :=
by { simp only [set.Icc, le_one', nonneg', and_self, set.set_of_true,
                set.univ_inter], }

def expand_bot_half : unit_interval → unit_interval :=
λ t, if h : t ≤ half then ⟨2*t, (mul_pos_mem_iff zero_lt_two).mpr ⟨nonneg',h⟩⟩ else 1

lemma expand_bot_half_monotone : monotone expand_bot_half := λ ⟨x,xl,xr⟩ ⟨y,yl,yr⟩ h,
begin
  dsimp only [expand_bot_half],
  split_ifs with h_1 h_2,
  { simpa only [subtype.mk_le_mk, mul_le_mul_left, zero_lt_bit0, zero_lt_one] using h, },
  { exact le_one' },
  { exfalso, exact h_1 (h.trans h_2), },
  { refl, },
end

lemma expand_bot_half_maps_to : (set.Icc 0 half).maps_to expand_bot_half (set.Icc 0 1) :=
by { simp only [Icc_zero_one], apply set.maps_to_univ, }

lemma expand_bot_half_surj_on : (set.Icc 0 half).surj_on expand_bot_half (set.Icc 0 1) :=
begin
  rintros ⟨x,xl,xr⟩ _,
  dsimp only [expand_bot_half],
  simp only [set.mem_Icc, subtype.mk_le_mk, subtype.coe_mk, set.mem_image, set_coe.exists],
  use x/2,
  refine ⟨⟨half_nonneg xl, (half_le_self xl).trans xr⟩,_⟩,
  sorry

end

def expand_top_half : unit_interval → unit_interval :=
λ t, if h : t ≤ half then 0 else
  ⟨2*↑t - 1, two_mul_sub_one_mem_iff.mpr ⟨le_of_lt (not_le.mp h),t.prop.right⟩⟩

lemma expand_top_half_monotone : monotone expand_top_half := λ ⟨x,xl,xr⟩ ⟨y,yl,yr⟩ h,
begin
  dsimp only [expand_top_half],
  split_ifs,
  { refl, },
  { exact nonneg', },
  { exfalso, exact h_1 (h.trans h_2), },
  { simp only [subtype.coe_mk, subtype.mk_le_mk, sub_le_sub_iff_right, mul_le_mul_left,
               zero_lt_bit0, zero_lt_one], exact h, },
end
lemma expand_top_half_maps_to : (set.Icc half 1).maps_to expand_top_half (set.Icc 0 1) :=
by { simp only [Icc_zero_one], apply set.maps_to_univ, }

lemma expand_top_half_surj_on : (set.Icc half 1).surj_on expand_top_half (set.Icc 0 1) :=
begin sorry end

end unit_interval

namespace path

lemma path.trans_eq_on_bot_half
  {X : Type*} [topological_space X] {x y z : X} (γ : path x y) (γ' : path y z):
  (set.Icc 0 unit_interval.half).eq_on (γ.trans γ') (γ ∘ unit_interval.expand_bot_half) :=
begin
  rintro ⟨t,_,_⟩ ⟨tl,tr⟩,
  dsimp only [unit_interval.expand_bot_half, path.trans],
  simp only [subtype.mk_le_mk, subtype.coe_mk, coe_mk, function.comp_app] at tl tr ⊢,
  split_ifs with h;
  { rw extend_extends, },
end

lemma path.trans_eq_on_top_half
  {X : Type*} [topological_space X] {x y z : X} (γ : path x y) (γ' : path y z):
  (set.Icc unit_interval.half 1).eq_on (γ.trans γ') (γ' ∘ unit_interval.expand_top_half) :=
begin
  rintro ⟨t,_,_⟩ ⟨tl,tr⟩,
  dsimp only [unit_interval.expand_top_half, path.trans],
  simp only [subtype.mk_le_mk, one_div, subtype.coe_mk, coe_mk, function.comp_app] at tl tr ⊢,
  split_ifs with h,
  { simp only [le_antisymm h tl, path.source, coe_mk, function.comp_app, subtype.coe_mk, le_refl,
               set.right_mem_Icc, zero_le_one, mul_inv_cancel_of_invertible, extend_extends,
               set.Icc.mk_one, path.target, if_true], },
  { rw extend_extends, },
end

end path

namespace path
variables {E : Type*} [pseudo_emetric_space E]

def length {x y : E} (p : path x y) : ennreal := evariation_on p.to_fun (set.univ)

lemma length_ge (x y : E) (p : path x y) : edist x y ≤ p.length :=
begin
  dsimp only [path.length],
  simp_rw  [←p.source', ←p.target'],
  apply evariation_on.edist_le; trivial,
end

lemma length_refl (x : E) : (path.refl x).length = 0 :=
begin
  apply evariation_on.constant_on,
  simp only [set.image_univ, continuous_map.to_fun_eq_coe, coe_to_continuous_map, refl_range,
             set.subsingleton_singleton],
end

lemma length_symm {x y : E} (p : path x y) : p.symm.length = p.length :=
begin
  dsimp only [path.length, path.symm, unit_interval.symm],
  apply evariation_on.comp_eq_of_antitone_on,
  { exact unit_interval.symm_anti.antitone_on _, },
  { simp only [set.maps_univ_to, set.mem_univ, forall_const], },
  { rw ←set.surjective_iff_surj_on_univ,
    exact unit_interval.symm_surj, }
end


lemma length_trans {x y z : E} (p : path x y) (q : path y z) :
  (p.trans q).length = p.length + q.length :=
begin
  change
    evariation_on ⇑(p.trans q) set.univ = evariation_on ⇑p set.univ + evariation_on ⇑q set.univ,
  have : set.univ = set.univ ∩ set.Icc (0 : unit_interval) (1 : unit_interval), by
  { simp only [unit_interval.Icc_zero_one, set.univ_inter], },
  rw this, clear this,
  rw ←evariation_on.Icc_add_Icc _ (unit_interval.nonneg' : 0 ≤ unit_interval.half)
                                  (unit_interval.le_one' : unit_interval.half ≤ 1) (set.mem_univ _),
  simp only [set.univ_inter],
  congr' 1,
  { rw ←evariation_on.comp_eq_of_monotone_on (⇑p) (unit_interval.expand_bot_half)
          (unit_interval.expand_bot_half_monotone.monotone_on _)
          (unit_interval.expand_bot_half_maps_to)
          (unit_interval.expand_bot_half_surj_on),
    apply evariation_on.eq_of_eq_on,
    apply path.trans_eq_on_bot_half, },
  { rw ←evariation_on.comp_eq_of_monotone_on (⇑q) (unit_interval.expand_top_half)
          (unit_interval.expand_top_half_monotone.monotone_on _)
          (unit_interval.expand_top_half_maps_to)
          (unit_interval.expand_top_half_surj_on),
    apply evariation_on.eq_of_eq_on,
    apply path.trans_eq_on_top_half, },
end

end path

def length_metric (E : Type*) [pseudo_emetric_space E] := E

variables {E : Type*} [pseudo_emetric_space E]

def to_length_metric : E → length_metric E := id
def from_length_metric : length_metric E → E := id

@[protected]
abbreviation of : E → length_metric E := to_length_metric
@[protected]
abbreviation fo : length_metric E → E := from_length_metric

instance : pseudo_emetric_space (length_metric E) :=
{ edist := λ x y, infi (λ (p : path (fo x) (fo y)), p.length),
  edist_self := λ x, by
  { refine le_antisymm _ zero_le',
    rw ←(path.length_refl $ fo x),
    refine infi_le _ _, },
  edist_comm := λ x y, by
  { apply le_antisymm;
    { refine le_infi (λ p, _),
      rw ←path.length_symm,
      refine infi_le _ _, }, },
  edist_triangle := λ x y z, by
  { simp_rw [ennreal.infi_add, ennreal.add_infi],
    apply le_infi₂ (λ p q, _),
    rw ←path.length_trans p q,
    exact infi_le _ (p.trans q), } }

lemma from_length_metric_nonexpanding :
  lipschitz_with 1 (from_length_metric : length_metric E → E) :=
begin
  rintro x y,
  simp only [edist, ennreal.coe_one, one_mul, le_infi_iff],
  apply path.length_ge,
end
