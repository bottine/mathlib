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
  apply evariation_on.comp_eq',
  { rintro x _ y _ h,
    simp only [subtype.mk_le_mk, sub_le_sub_iff_left, subtype.coe_le_coe],
    exact h, },
  { simp only [set.maps_univ_to, set.mem_univ, forall_const], },
  { rintro ⟨x,xle,xge⟩ h,
    simp only [set.image_univ, set.mem_range, subtype.mk_eq_mk, set_coe.exists, set.mem_Icc,
               subtype.coe_mk, exists_prop],
    use 1-x,
    simp only [xle, xge, sub_nonneg, sub_le_self_iff, and_self, sub_sub_cancel,
               eq_self_iff_true], },
end

lemma length_trans {x y z : E} (p : path x y) (q : path y z) :
  (p.trans q).length = p.length + q.length :=
begin
  dsimp [path.length, path.trans],
  let half : unit_interval := ⟨1/2, by {simp only [one_div, inv_nonneg, zero_le_bit0, zero_le_one],}, sorry⟩,
  /-
  lemma Icc_add_Icc (f : α → E) {s : set α} {a b c : α}
  (hab : a ≤ b) (hbc : b ≤ c) (hb : b ∈ s) :
  evariation_on f (s ∩ Icc a b) + evariation_on f (s ∩ Icc b c) = evariation_on f (s ∩ Icc a c) :=
  -/
  rw evariation_on.Icc_and_Icc (0 ≤ half),
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
