/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.measure.lebesgue
import analysis.calculus.monotone
import data.set.function


open_locale big_operators nnreal ennreal
open set measure_theory

variables {α β : Type*} [linear_order α] [linear_order β]
{E F : Type*} [pseudo_emetric_space E] [pseudo_emetric_space F]
{V : Type*} [normed_add_comm_group V] [normed_space ℝ V] [finite_dimensional ℝ V]


namespace bounded_variation

lemma sum_le_sum_of_range_sub_range (f : α → E) {s : set α}
  {n : ℕ} {u : ℕ → α} (hu : monotone_on u (Iic n)) (us : ∀ i ≤ n, u i ∈ s)
  {m : ℕ} {v : ℕ → α} (hv : monotone_on v (Iic m)) (vs : ∀ i ≤ m, v i ∈ s)
  (uv : u '' (Iic n) ⊆ v '' (Iic m)) :
  ∑ i in finset.range n, edist (f (u (i+1))) (f (u i))
  ≤ ∑ i in finset.range m, edist (f (v (i+1))) (f (v i)) :=
begin
  induction m,
  { simp only [*, nat.nat_zero_eq_zero, finset.range_zero, finset.sum_empty, le_zero_iff,
               finset.sum_eq_zero_iff, finset.mem_range, forall_eq] at *,
    have : Iic 0 = {0}, by {dsimp [set.Iic], simp, },
    simp only [this, image_singleton, monotone_on_singleton, eq_self_iff_true] at *,
     },
  { rw finset.sum_range_succ, }
end


end bounded_variation
