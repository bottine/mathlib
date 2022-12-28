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

namespace unit_interval

/-- The midpoint of the unit interval -/
abbreviation half : unit_interval := ⟨1/2, div_mem zero_le_one zero_le_two one_le_two ⟩

@[simp] lemma symm_half : symm half = half :=
subtype.ext $ by { simp only [symm], exact sub_half 1, }

@[simp] lemma symm_inv : symm.involutive := symm_symm
@[simp] lemma symm_inj : symm.injective := symm_inv.injective
@[simp] lemma symm_surj : symm.surjective := symm_inv.surjective
@[simp] lemma symm_anti : antitone symm :=
begin
  rintro x y h,
  simp only [symm, subtype.mk_le_mk, sub_le_sub_iff_left, subtype.coe_le_coe],
  exact h,
end

@[simp] lemma Icc_zero_one : set.Icc (0 : unit_interval) (1 : unit_interval) = set.univ :=
by { simp only [set.Icc, unit_interval.le_one', unit_interval.nonneg', and_self, set.set_of_true,
                set.univ_inter], }

def expand_bot_half : unit_interval → unit_interval :=
λ t, if h : t ≤ half then ⟨2*↑t, sorry⟩ else 1

def expand_top_half : unit_interval → unit_interval :=
λ t, if h : t ≤ half then 0 else
  ⟨2*↑t - 1, two_mul_sub_one_mem_iff.mpr ⟨le_of_lt (not_le.mp h),t.prop.right⟩⟩

lemma expand_top_half_monotone : monotone expand_top_half := sorry
lemma expand_top_half_maps_to : (set.Icc half 1).maps_to expand_top_half (set.Icc 0 1) := sorry
lemma expand_top_half_surj_on : (set.Icc half 1).surj_on expand_top_half (set.Icc 0 1) := sorry

end unit_interval

namespace path

lemma path.trans_eq_on_bot_half
  {X : Type*} [topological_space X] {x y z : X} (γ : path x y) (γ' : path y z):
  (set.Icc 0 unit_interval.half).eq_on (γ.trans γ') (γ ∘ unit_interval.expand_bot_half) := sorry

lemma path.trans_eq_on_top_half
  {X : Type*} [topological_space X] {x y z : X} (γ : path x y) (γ' : path y z):
  (set.Icc unit_interval.half 1).eq_on (γ.trans γ') (γ' ∘ unit_interval.expand_top_half) := sorry


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
  dsimp [path.length, path.symm, unit_interval.symm],
  apply evariation_on.comp_eq_of_antitone_on,
  { exact unit_interval.symm_anti.antitone_on _, },
  { simp only [set.maps_univ_to, set.mem_univ, forall_const], },
  { rw ←set.surjective_iff_surj_on_univ,
    exact unit_interval.symm_surj, }
end



lemma length_trans {x y z : E} (p : path x y) (q : path y z) :
  (p.trans q).length = p.length + q.length :=
begin
  dsimp [path.length],
  have : set.univ = set.univ ∩ set.Icc (0 : unit_interval) (1 : unit_interval), by
  { simp only [unit_interval.Icc_zero_one, set.univ_inter], },
  rw this, clear this,
  rw ←evariation_on.Icc_add_Icc _ (unit_interval.nonneg' : 0 ≤ unit_interval.half)
                                  (unit_interval.le_one' : unit_interval.half ≤ 1) (set.mem_univ _),
  simp only [set.univ_inter],
  congr' 1,
  { sorry, },
  { rw ←evariation_on.comp_eq_of_monotone_on (⇑q) (unit_interval.expand_top_half)
          (unit_interval.expand_top_half_monotone.monotone_on _)
          (unit_interval.expand_top_half_maps_to)
          (unit_interval.expand_top_half_surj_on),
    apply evariation_on.eq_of_eq_on,
    apply path.trans_eq_on_top_half,
    /-rintro ⟨t,zt,_⟩ ⟨le_t,t_le⟩,
    dsimp only [unit_interval.expand_top_half],
    simp only [subtype.coe_mk, one_div, function.comp_app, subtype.mk_le_mk] at *,
    split_ifs,
    { simp only [le_antisymm h le_t, set.right_mem_Icc, zero_le_one, mul_inv_cancel_of_invertible,
                 extend_extends, set.Icc.mk_one, path.target, path.source], },
    { have : 2 * t - 1 ∈ unit_interval, by
      { rw [unit_interval.two_mul_sub_one_mem_iff, one_div],
        exact ⟨le_t, t_le⟩, },
      rw extend_extends _ this, }; sorry,-/ },
end

end path

def length_metric (E : Type*) [pseudo_emetric_space E] := E

variables {E : Type*} [pseudo_emetric_space E]

def of : E → length_metric E := id
def fo : length_metric E → E := id


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
  edist_triangle := sorry }

lemma of_is_nonexpanding : lipschitz_with 1 (of : E → length_metric E) :=
begin
  rintro x y,
  dsimp only [edist],
  sorry,
end
