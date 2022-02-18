/-
Copyright (c) 2022 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import topology.metric_space.basic
import topology.metric_space.coarse.basic
/-!
# Coarse Lipschitz maps

Todo

## Main result

Todo

## References

* [C. Druțu and M. Kapovich **Geometric group theory**][MR3753580]

## Tags

coarse geometry, metric space
-/
universes u v w x

open function set fintype function
open_locale nnreal

variables {α : Type u} [pseudo_metric_space α]
          {β : Type v} [pseudo_metric_space β]
          {γ : Type w} [pseudo_metric_space γ]
          {δ : Type x} [pseudo_metric_space δ]


/--
Given pseudo-metric spaces `α` and `β`, the map `f : α → β` is (coarse) `(K,L)`-(coarse) Lipschitz
if given any `x y : α`, we have `dist (f x) (f y) ≤ L + K * (dist x y)`.
-/
def coarse_lipschitz_with (K L : ℝ≥0) (f : α → β) := ∀ x y, dist (f x) (f y) ≤ L + K * dist x y


namespace coarse_lipschitz_with

lemma of_dist_le {f : α → β} (h : ∀ x y, dist (f x) (f y) ≤ dist x y) :
  coarse_lipschitz_with 1 0 f :=
λ x y, by simp only [nnreal.coe_one, nnreal.coe_zero, zero_add, one_mul, h]

@[protected]
lemma const (b : β) : coarse_lipschitz_with 0 0 (λa:α, b) :=
λ x y, by simp only [dist_self, zero_le]

@[protected]
lemma id : coarse_lipschitz_with 1 0 (@id α) :=
  of_dist_le $ assume x y, le_rfl

lemma weaken {f : α → β} {K L K' L' : ℝ≥0}
  (hf : coarse_lipschitz_with K L f) (hK : K ≤ K') (hL : L ≤ L') :
  coarse_lipschitz_with K' L' f :=
λ x y, le_trans (hf x y) $ le_add_mul (nnreal.coe_le_coe.2 hL) (nnreal.coe_le_coe.2 hK) (le_rfl)

lemma comp
  {Kf Lf : ℝ≥0} {f : α → β} (clf : coarse_lipschitz_with Kf Lf f)
  {Kg Lg : ℝ≥0} {g : β → γ} (clg : coarse_lipschitz_with Kg Lg g) :
  coarse_lipschitz_with (Kg * Kf) (Lg + Kg * Lf) (g ∘ f) :=
begin
  intros x y,
  calc dist ((g ∘ f) x)  ((g ∘ f) y) = dist (g (f x)) (g (f y)) : by simp
                                  ... ≤ Lg + Kg * (dist (f x) (f y)) : clg (f x) (f y)
                                  ... ≤ Lg + Kg * (Lf + Kf * dist x y)
                                      : le_add_mul (le_rfl) (le_rfl) (clf x y)
                                  ... = (Lg + Kg * Lf ) + (Kg * Kf) * dist x y : by ring
                                  ... = ↑(Lg + Kg * Lf ) + ↑(Kg * Kf) * dist x y : by simp,

end

/--
A map close to a coarse Lipschitz map is itself coarse Lipschitz
-/
lemma of_close_maps_with {C K L : ℝ≥0} {f f' : α → β }
  (c : close_maps_with C f f') (clf : coarse_lipschitz_with K L f) :
  coarse_lipschitz_with  K (2*C + L) f' :=
λ x y, calc dist (f' x) (f' y) ≤ dist (f' x) (f x) + dist (f x) (f y)   + dist (f y) (f' y)
                                : dist_triangle4 (f' x) (f x) (f y) (f' y)
                            ... ≤ ↑C                  + (↑L + ↑K * (dist x y)) + ↑C
                                : add_le_add (add_le_add ((close_maps_with.symm c) x) (clf x y)) (c y)
                            ... = (2*↑C + ↑L) + ↑K * (dist x y)
                                : by ring
                            ... = ↑(2*C + L) + ↑K * (dist x y)
                                : by simp

@[protected]
lemma coe {s : set α} : coarse_lipschitz_with 1 0 (coe: subtype s → α) :=
λ x y, by {rw ← subtype.dist_eq, simp}

@[protected]
lemma iff_range_factorization_is (K L: ℝ≥0) (f : α → β)  :
  coarse_lipschitz_with K L f ↔ coarse_lipschitz_with K L (range_factorization f) :=
by simp only [coarse_lipschitz_with, subtype.dist_eq, range_factorization_coe]

end coarse_lipschitz_with


namespace coarsely_dense_with_in

/--
Coarse Lipschitz maps preserve “being coarsely dense in”.
-/
lemma of_coarse_lipschitz_images
  {K L : ℝ≥0} {f : α → β} (clf : coarse_lipschitz_with K L f)
  {ε : ℝ≥0} {s t : set α} (cdwi : coarsely_dense_with_in ε s t) :
  coarsely_dense_with_in (L + K*ε) (f '' s) (f '' t) :=
begin
  rintros _ ⟨x,xt,rfl⟩,
  rcases cdwi xt with ⟨y,ys,yd⟩,
  use [f y, mem_image_of_mem f ys],
  calc dist (f x) (f y) ≤ ↑L + ↑K * dist x y  : clf _ _
                     ... ≤ ↑L + ↑K * ↑ε         : le_add_mul (le_refl ↑L) (le_refl ↑K) yd
                     ... ≤ ↑(L + K * ε)         : by simp,
end

end coarsely_dense_with_in
