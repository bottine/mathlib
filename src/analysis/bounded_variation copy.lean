/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.measure.lebesgue
import analysis.calculus.monotone
import data.set.function
import .bounded_variation
import topology.instances.ennreal


open_locale big_operators nnreal ennreal
open set measure_theory
open classical
open ennreal
local attribute [instance, priority 10] prop_decidable

set_option profiler true

--set_option pp.implicit true
variables {α β : Type*} [linear_order α] [linear_order β]
{E F : Type*} [pseudo_emetric_space E] [pseudo_emetric_space F]
{V : Type*} [normed_add_comm_group V] [normed_space ℝ V] [finite_dimensional ℝ V]

namespace evariation_on

lemma _root_.edist_congr_left {a b c : E} (hab : edist a b = 0) : edist a c = edist b c :=
begin
  apply le_antisymm,
  rw [←zero_add (edist b c), ←hab],
  apply edist_triangle,
  rw edist_comm at hab,
  rw [←zero_add (edist a c), ←hab],
  apply edist_triangle,
end

lemma _root_.edist_congr_right {a b c : E} (hab : edist a b = 0) : edist c a = edist c b :=
by { rw [edist_comm c a, edist_comm c b], apply edist_congr_left hab,  }

lemma _root_.ennreal.mul_div_mul_left {a b c : ℝ≥0∞} (ha : a ≠ 0) (ha' : a ≠ ⊤) :
  a * b / (a * c) = b / c := sorry




lemma eq_of_edist_zero_on {f f' : α → E} {s : set α} (h : ∀ ⦃x⦄, x ∈ s → edist (f x) (f' x) = 0) :
  evariation_on f s = evariation_on f' s :=
begin
  dsimp only [evariation_on],
  congr' 1 with p : 1,
  congr' 1 with i : 1,
  rw edist_congr_left (h $ p.snd.prop.2 (i+1)),
  rw edist_congr_right (h $ p.snd.prop.2 i),
end


/-
 theorem metric.tendsto_uniformly_on_iff {α : Type u} {β : Type v} [pseudo_metric_space α]
 {ι : Type u_1} {F : ι → β → α} {f : β → α} {p : filter ι} {s : set β} :
tendsto_uniformly_on F f p s ↔ ∀ (ε : ℝ), ε > 0 → (∀ᶠ (n : ι) in p, ∀ (x : β), x ∈ s → has_dist.dist (f x) (F n x) < ε)

-/

lemma eps_approx {f : α → E} {s : set α} (hs: s.nonempty) (h : has_bounded_variation_on f s)
  (ε : ℝ≥0∞) (hε : ε > 0) :
  ∃ (p : ℕ × {u : ℕ → α // monotone u ∧ ∀ i, u i ∈ s}), evariation_on f s
    ≤ ∑ i in finset.range p.1, edist (f ((p.2 : ℕ → α) (i+1))) (f ((p.2 : ℕ → α) i)) + ε  :=
begin
  haveI := nonempty_monotone_mem hs,
  by_contra' hn,
  apply (ennreal.lt_add_right h (ne_of_lt hε).symm).not_le,
  dsimp only [evariation_on],
  rw [ennreal.supr_add],
  exact supr_le (λ h, (hn h).le),
end

lemma evariation_on_lower_continuous {ι : Type*} {F : ι → α → E} {p : filter ι}
  {f : α → E} {s : set α} (hF : tendsto_uniformly_on F f p s) (hf : has_bounded_variation_on f s) :
  ∀ (ε : ℝ≥0), ε ≠ 0 → (∀ᶠ (n : ι) in p, evariation_on f s ≤ evariation_on (F n) s + ε) :=
begin
  by_cases hs : s.nonempty, swap,
  { simp only [evariation_on.subsingleton f (λ x hx _ _, (hs ⟨x,hx⟩).elim),
               zero_le', filter.eventually_true, implies_true_iff], },
  rintro ε hε,
  rw emetric.tendsto_uniformly_on_iff at hF,
  obtain ⟨⟨n,⟨u,um,us⟩⟩,hlt⟩ := eps_approx hs hf ((ε : ℝ≥0∞)/2) (half_pos (coe_ne_zero.mpr hε)),
  specialize hF ((ε : ℝ≥0∞)/(4*n))
    (ennreal.div_pos_iff.mpr ⟨coe_ne_zero.mpr hε, mul_ne_top (coe_ne_top) (coe_ne_top)⟩),
  refine (hF.mono $ λ i hi, hlt.trans (le_trans _ (add_le_add_right (sum_le (F i) n um us) ε))),
  clear hlt hF,
  have : (ε : ℝ≥0∞) = (↑ε/2) + (↑ε/2), simp only [ennreal.add_halves],
  nth_rewrite_rhs 0 this, rw ←add_assoc,
  refine add_le_add_right _ _,
  calc ∑ (j : ℕ) in finset.range n, edist (f (u j.succ)) (f (u j))
     ≤ ∑ (j : ℕ) in finset.range n, (edist (F i (u j.succ)) (F i (u j)) + ↑ε/(2*n)) : by
  begin
    refine finset.sum_le_sum (λ j jn, _),
    apply (edist_triangle4 _ (F i (u j.succ)) (F i (u j)) _).trans,
    have : (ε : ℝ≥0∞)/(2*↑n) = ε/(4*n) + ε/(4*n), by
    { rw [ennreal.div_add_div_same, ←two_mul,
          (by {norm_cast, rw ←mul_assoc, refl, } : (4 : ennreal) * ↑n = 2 * (2 * ↑n)),
          ennreal.mul_div_mul_left (ennreal.two_ne_zero) (ennreal.two_ne_top)], },
    rw [this, ←add_assoc],
    refine add_le_add _ _,
    { nth_rewrite_lhs 0 add_comm, refine add_le_add_left ((hi (u j.succ) (us j.succ)).le) _, },
    { rw edist_comm, exact (hi (u j) (us j)).le,  }
  end
  ...= ∑ (j : ℕ) in finset.range n, edist (F i (u j.succ)) (F i (u j)) + n*(↑ε/(2*n)) :
  by  simp only [finset.sum_add_distrib, finset.sum_const, finset.card_range, nsmul_eq_mul]
  ...≤ ∑ (j : ℕ) in finset.range n, edist (F i (u j.succ)) (F i (u j)) + (↑ε/2) : by
  begin
    refine add_le_add_left _ _,
    rw [ennreal.le_div_iff_mul_le (or.inl ennreal.two_ne_zero) (or.inl ennreal.two_ne_top),
        mul_comm, ←mul_assoc, mul_comm ((2 : ℝ≥0∞) * ↑n)],
    apply ennreal.mul_le_of_le_div (le_refl _),
  end
end

end evariation_on

namespace has_locally_bounded_variation_on

variables {f : α → E} {s : set α} (hf : has_locally_bounded_variation_on f s)


noncomputable def arc_length_parameterization_or {a : α} (as : a ∈ s) (e : E) : ℝ → E :=
λ x, if h : ∃ b, b ∈ s ∧ x = hf.variation_from_to a b then f h.some else e

/--
In a metric space, precomposing arc-length parameterization with variation yields the original
map.
-/
lemma arc_length_parameterization_edist_zero {a : α} (as : a ∈ s) {b : α} (bs : b ∈ s) (e : E) :
  edist (f b) (hf.arc_length_parameterization_or as e (hf.variation_from_to a b)) = 0 :=
begin
  classical,
  dsimp only [arc_length_parameterization_or],

  let cc : ∃ (b : α), b ∈ s ∧ hf.variation_from_to a b = hf.variation_from_to a b := ⟨b, bs, rfl⟩,
  rw dif_pos, swap, exact cc,
  /-let c := cc.some,
  let cs := cc.some_spec.1,
  let cb := cc.some_spec.2,
  rw [←hf.variation_from_to_add as bs cs, add_right_eq_self] at cb,
  rw [←ennreal.bot_eq_zero, eq_bot_iff, ennreal.bot_eq_zero],
  by_cases h : b ≤ c,
  { rw [←ennreal.of_real_zero, ←cb, hf.variation_from_to_eq_of_le h,
        ennreal.of_real_to_real (hf b c bs cs)],
    apply evariation_on.edist_le f,
    exact ⟨bs, ⟨le_refl _, h⟩⟩,
    exact ⟨cs, ⟨h, le_refl _⟩⟩, },
  { replace h : c ≤ b := (lt_of_not_le h).le,
    rw [hf.variation_from_to_eq_neg_swap, neg_eq_zero] at cb,
    rw [edist_comm, ←ennreal.of_real_zero, ←cb, hf.variation_from_to_eq_of_le h,
        ennreal.of_real_to_real (hf c b cs bs)],
    apply evariation_on.edist_le f,
    exact ⟨cs, ⟨le_refl _, h⟩⟩,
    exact ⟨bs, ⟨h, le_refl _⟩⟩, }-/
end


lemma arc_length_parameterization_unit_length {a : α} (as : a ∈ s) {x y} (xy : x ≤ y) :
  evariation_on (hf.arc_length_parameterization as) (Icc x y) = edist x y :=
begin
  dsimp only [arc_length_parameterization],
  obtain ⟨x,hx⟩ := x,
  obtain ⟨y,hy⟩ := y,
  let c := hx.some,
  let cs := hx.some_spec.1,
  let cx := hx.some_spec.2,
  let d := hy.some,
  let ds := hy.some_spec.1,
  let dy := hy.some_spec.2,
  sorry,
end

end has_locally_bounded_variation_on
