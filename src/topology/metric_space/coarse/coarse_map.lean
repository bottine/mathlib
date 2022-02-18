/-
Copyright (c) 2022 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import topology.metric_space.basic
import topology.metric_space.coarse.basic
/-!
# Controlled maps

Todo

## Main result

Todo

## References

* [C. Druțu and M. Kapovich **Geometric group theory**][MR3753580]

## Tags

coarse geometry, metric space
-/
universes u v w x

open function set fintype function pseudo_metric_space
open_locale nnreal

variables {α : Type u} [pseudo_metric_space α]
          {β : Type v} [pseudo_metric_space β]
          {γ : Type w} [pseudo_metric_space γ]
          {δ : Type x} [pseudo_metric_space δ]


def controlled_with (Φ : ℝ → ℝ) (Φm : monotone Φ) (f : α → β) :=
∀ x y, dist (f x) (f y) ≤ Φ (dist x y)

namespace controlled_with

lemma of_dist_le {f : α → β} (h : ∀ x y, dist (f x) (f y) ≤ dist x y) :
  controlled_with id monotone_id f := h

@[protected]
lemma const (b : β) : controlled_with (λ x, 0) monotone_const (λa:α, b) :=
λ x y, by simp

@[protected]
lemma id : controlled_with id monotone_id (@id α) :=
  of_dist_le $ assume x y, le_rfl

lemma weaken {f : α → β} (Φ Φ' : ℝ → ℝ) {Φm : monotone Φ} {Φ'm : monotone Φ'}
  (hf : controlled_with Φ Φm f) (hΦ : ∀ x, (Φ x) ≤ (Φ' x)) :
  controlled_with Φ' Φ'm f :=
λ x y, le_trans (hf x y) $ hΦ (dist x y)


lemma comp
  {Φf : ℝ → ℝ} {Φfm : monotone Φf} {f : α → β} (clf : controlled_with Φf Φfm f)
  {Φg : ℝ → ℝ} {Φgm : monotone Φg} {g : β → γ} (clg : controlled_with Φg Φgm g) :
  controlled_with (Φg ∘ Φf) (Φgm.comp Φfm) (g ∘ f) :=
  λ x y, calc dist ((g ∘ f) x)  ((g ∘ f) y) ≤ Φg (dist (f x) (f y)) : clg (f x) (f y)
                                       ...  ≤ Φg (Φf (dist x y)) : Φgm (clf x y)

lemma of_close_maps_with {C : ℝ} {Φ : ℝ → ℝ} {Φm : monotone Φ} {f f' : α → β }
  (c : close_maps_with C f f') (clf : controlled_with Φ Φm f) :
  controlled_with  (λ x, Φ x + 2*C) {!!} f'  :=
λ x y, calc dist (f' x)                                       (f' y)
          ≤ dist (f' x) (f x) + dist (f x) (f y) + dist (f y) (f' y) : dist_triangle4 _ _ _ _
      ... ≤ C                 + dist (f x) (f y) + dist (f y) (f' y) : add_le_add (add_le_add (c.symm x) le_rfl) le_rfl
      ... ≤ C                 + dist (f x) (f y) + C                 : add_le_add le_rfl (c y)
      ... ≤ 2*C               + dist (f x) (f y)                     : by ring_nf
      ... ≤ 2*C               + Φ (dist x y)                         : add_le_add le_rfl (clf x y)
      ... = 2*C + Φ (dist x y)                                       : by ring

@[protected]
lemma coe {s : set α} : controlled_with id monotone_id (coe: subtype s → α) :=
λ x y, by {rw ← subtype.dist_eq, simp}

@[protected]
lemma iff_range_factorization_is (Φ : ℝ → ℝ) (Φm : monotone Φ) (f : α → β)  :
  controlled_with Φ Φm f ↔ controlled_with Φ Φm (range_factorization f) :=
by simp only [controlled_with, subtype.dist_eq, range_factorization_coe]

end controlled_with


namespace coarsely_dense_with_in

lemma of_coarse_images
  {Φ : ℝ → ℝ} {Φm : monotone Φ} {f : α → β} (clf : controlled_with Φ Φm f)
  {ε : ℝ} {s t : set α} (cdwi : coarsely_dense_with_in ε s t) :
  coarsely_dense_with_in (Φ ε) (f '' s) (f '' t) :=
begin
  rintros _ ⟨x,xt,rfl⟩,
  rcases cdwi xt with ⟨y,ys,yd⟩,
  use [f y, mem_image_of_mem f ys],
  calc  dist (f x) (f y)
      ≤ Φ (dist x y)  : clf _ _
  ... ≤ Φ ε           : Φm yd,
end

end coarsely_dense_with_in
