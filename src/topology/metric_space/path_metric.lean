/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import analysis.bounded_variation
import topology.metric_space.emetric_space
import topology.path_connected
import data.real.ennreal
import data.real.ereal

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

-- should use data.set.intervals.proj_Icc ?
-- this is not really the same thing…
def expand_Icc {a b : unit_interval} (h : a ≤ b) : unit_interval → unit_interval :=
λ t, if lta : t < a then 0 else if gtb : b < t then 1 else
  ⟨ (t - a) / (b - a), by
    { apply div_mem;
      simp only [sub_nonneg, subtype.coe_le_coe, not_lt, sub_le_sub_iff_right] at *; assumption, } ⟩

def shrink_to_Icc {a b : unit_interval} (h : a ≤ b) : unit_interval → unit_interval :=
λ t, ⟨a + t * (b - a), sorry⟩

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

section length_on

variables {x y : E} (p : path x y) (s t : unit_interval)

def length_on : ereal :=
if s ≤ t then   evariation_on p.to_fun (set.Icc s t)
         else - evariation_on p.to_fun (set.Icc t s)

lemma length_on_eq : p.length_on s s = 0 :=
begin
  dsimp only [length_on],
  split_ifs,
  { simp only [set.Icc_self, evariation_on.subsingleton, set.subsingleton_singleton,
               ereal.coe_ennreal_zero], },
  { exact (h (le_refl _)).elim, }
end

lemma length_on_le (h : s ≤ t) : p.length_on s t ≥ 0 :=
begin
  dsimp only [length_on],
  split_ifs with st,
  { exact ereal.coe_ennreal_nonneg _, },
end

lemma length_on_ge (h : t ≤ s) : p.length_on s t ≤ 0 :=
begin
  dsimp only [length_on],
  split_ifs with st ts,
  { cases le_antisymm h st,
    simp only [set.Icc_self, evariation_on.subsingleton,
               set.subsingleton_singleton, ereal.coe_ennreal_zero, le_refl], },
  { rw [ereal.neg_le, neg_zero], positivity, },
end

lemma length_on_add (r s t) : p.length_on r s + p.length_on s t = p.length_on r t :=
begin
  dsimp only [length_on],
  split_ifs,
  { sorry, },
  { exact (h_2 (h.trans h_1)).elim, },
  { sorry },
  { sorry },
  { sorry },
  { sorry },
  { exact (h (h_2.trans (not_le.mp h_1).le)).elim, },
  { sorry },

end

/--
If `p` is rectifiable on the segment `[s,t]`, and `ε>0` is given, there exists a partition
of `[s,t]` such that the length of `p` on each part is less than `ε`.
Stated in terms of monotone functions for compatibility with `bounded_variation`
-/
lemma split_for_small_length_on (st : s ≤ t) (hp : p.length_on s t < ⊤) (ε : nnreal) :
  -- There exists a natural (say `n`) and a monotone function `u` with values in the interval
  -- (we only care about `u 0 … u n`)
  ∃ (q : ℕ × {u : ℕ → unit_interval // monotone u ∧ ∀ i, u i ∈ set.Icc s t}),
  -- such that `u 0 = s`
  q.2.1 0 = s ∧
  -- and `u n = t`
  q.2.1 q.1 = t ∧
  -- and the length of `p` on each interval `[u i, u i.succ]` is less than `ε`
  ∀ i : finset.range q.1, p.length_on (q.2.1 i) (q.2.1 (i+1)) < ε :=
begin
  sorry,
end

lemma length_from_monotone : monotone (p.length_on s) := sorry
lemma length_to_antitone : antitone (λ s, p.length_on s t) := sorry
lemma length_on_monotone (s' t') (ss' : s ≤ s') (tt' : t' ≤ t) :
  p.length_on s' t' ≤ p.length_on s t := sorry


lemma length_on_diff {s' t'} :
  edist (p.length_on s t) (p.length_on s' t') ≤ |(p.length_on s s')| + |(p.length_on t t')| := sorry

lemma length_on_continuous  : continuous (p.length_on) :=
begin
  -- Fix s t, and ε.
  -- Choose a partition of the interval such that the restriction of `p` on those segments is lt ε/2.
  -- If `s ∈ [u i, u i.succ]` and `t ∈ [u j, u j.succ]`
  -- let `δ` be the min of `d (u i-1) (u i), d(u i, u i+1), d (u j-1) (u j), d (u j) (u j+1)`.
  -- Then if `s',t'` are within `δ` of `s,t` respectively, then the rerstiction of `p` on `[s,s']` and
  -- `[t,t']` will be < `ε`, and we can apply the lemma above.
  sorry
end

end length_on
/-
def length {x y : E} (p : path x y) : ennreal := evariation_on p.to_fun (set.univ)

lemma length_eq_length_on {x y : E} (p : path x y) : ↑p.length = p.length_on 0 1 := sorry

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

lemma from_length_metric_continuous : continuous (from_length_metric : length_metric E → E) :=
from_length_metric_nonexpanding.continuous

/--
Self note: `path_connected_space_iff_connected_space` and `is_connected_iff_is_path_connected` then
show that connected and path-connected components agree
-/
lemma locally_path_connected [nonempty E] : loc_path_connected_space (length_metric E) := sorry



lemma path.continuous_of_finite_length {x y : E} (p : path x y) (hpl : p.length < ⊤) :
  continuous (to_length_metric ∘ p) :=
begin

end
-/
