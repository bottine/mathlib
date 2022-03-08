/-
Copyright (c) 2019 Michael Howes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/


import group_theory.free_group
import group_theory.quotient_group
import data.real.ennreal
import data.nat.enat
import topology.metric_space.basic
import topology.metric_space.coarse.basic
import topology.metric_space.coarse.coarse_map

open option
open set function list
open well_founded
open classical
open_locale classical

/-!
# Defining a group given by generators and relations

## Main definitions


## Tags

generators, relations, group presentations
-/

noncomputable theory


def is_generated (G : Type*) [group G] {ι : Type*} (letters : ι → G) : Prop :=
∀ g : G, ∃ (w : free_group ι), free_group.lift letters w = g

@[class]
structure generated  (G : Type*) [group G] {ι : Type*} (letters : ι → G)  :=
(generated : is_generated G letters)





variables {G : Type*} [group G]

def finite_balls_left_invariant_control_fun
  (m₁ : pseudo_metric_space G) (loc_fin₁ : @finite_balls G m₁)
  (left_inva₁ : ∀ g h : G, @dist _ m₁.to_has_dist g h = @dist _ m₁.to_has_dist (1:G) ((g ⁻¹) * h))
  (m₂ : pseudo_metric_space G) (loc_fin₂ : @finite_balls G m₁)
  (left_inva₂ : ∀ g h : G, @dist _ m₂.to_has_dist g h = @dist _ m₂.to_has_dist (1:G) ((g ⁻¹) * h)) :
ℝ → ℝ :=
  λ r, @finset.sup ℝ G _ _ (@finset.univ (@metric.ball _ m₁ (1:G) r) _) (@dist _ m₂.to_has_dist (1:G))

def finite_balls_left_invariant_control_fun_monotone
  (m₁ : pseudo_metric_space G) (loc_fin₁ : @finite_balls G m₁)
  (left_inva₁ : ∀ g h : G, @dist _ m₁.to_has_dist g h = @dist _ m₁.to_has_dist (1:G) ((g ⁻¹) * h))
  (m₂ : pseudo_metric_space G) (loc_fin₂ : @finite_balls G m₁)
  (left_inva₂ : ∀ g h : G, @dist _ m₂.to_has_dist g h = @dist _ m₂.to_has_dist (1:G) ((g ⁻¹) * h)) :
  monotone $ finite_balls_left_invariant_control_fun m₁ loc_fin₁ left_inva₁ m₂ loc_fin₂ left_inva₂ :=
begin
  rintros r s rles,
  unfold finite_balls_left_invariant_control_fun,
  have := @metric.ball_subset_ball _ m₁ (1:G) _ _ rles,
  have := image_subset (@dist _ m₂.to_has_dist (1:G)) this,
  exact Sup_le_Sup this,
end


lemma finite_balls_left_invariant_are_coarsely_equivalent
  (m₁ : pseudo_metric_space G) (loc_fin₁ : @finite_balls G m₁)
  (left_inva₁ : ∀ g h : G, @dist _ m₁.to_has_dist g h = @dist _ m₁.to_has_dist (1:G) ((g ⁻¹) * h))
  (m₂ : pseudo_metric_space G) (loc_fin₂ : @finite_balls G m₁)
  (left_inva₂ : ∀ g h : G, @dist _ m₂.to_has_dist g h = @dist _ m₂.to_has_dist (1:G) ((g ⁻¹) * h)) :
  ∃ Φ : ℝ → ℝ, ∃ mΦ : monotone Φ,  @controlled_with G m₁ G m₂  Φ mΦ (@id G) :=
begin
  let Φ : ℝ → ℝ =
end



variables {ι : Type*} (letters : ι → G) [gen : generated G letters]


def val : (free_group ι) → G := λ w, free_group.lift letters w
def len : (free_group ι) → ℕ := λ w, (free_group.to_word w).length

def words_for (g : G) : set (free_group ι) :=
{ w : free_group ι | val letters w = g }
def geods_for  (g : G) : set (free_group ι) :=
{ w ∈  words_for letters g | ∀ u ∈ words_for letters g, (len u) ≥ (len w) }

lemma words_for_nonempty (g : G) [gen : generated G letters] : (words_for letters g).nonempty :=
begin -- why can't I directly call `gen.1 g` ???
  let lol := gen.1,
  exact lol g,
end

lemma geods_have_same_length
  (g : G) (w₁ w₂ : geods_for letters g) : len (w₁ : free_group ι) = len (w₂ : free_group ι) :=
let
  ⟨f₁,word₁,geod₁⟩ := w₁
, ⟨f₂,word₂,geod₂⟩ := w₂
in
  ge_antisymm (geod₂ f₁ word₁) (geod₁ f₂ word₂)



def geod_for (g : G)  [gen : generated G letters] : geods_for letters g :=
let
  wg := words_for letters g
, w := argmin_on len nat.lt_wf wg (words_for_nonempty letters gen g)
, w_word_for_g := argmin_on_mem len nat.lt_wf wg h
, w_shortest   := λ (w' : free_group ι) (w'_in : w' ∈ wg), argmin_on_le len nat.lt_wf wg w'_in h
in
  ⟨w,w_word_for_g,w_shortest⟩


def geod_for_helper (g : G)
  (emp : psum (words_for letters g).nonempty ¬(words_for letters g).nonempty ) :
  option (geods_for letters g) :=
let
  wg := words_for letters g
in
  psum.rec
    ( λ h,  let
        w := argmin_on len nat.lt_wf wg h
      , w_word_for_g := argmin_on_mem len nat.lt_wf wg h
      , w_shortest   := λ (w' : free_group ι) (w'_in : w' ∈ wg), argmin_on_le len nat.lt_wf wg w'_in h
      in
        option.some ( ⟨w,w_word_for_g,w_shortest⟩ : geods_for letters g ))
    ( λ h, none)
    emp

def get_emp (g : G) :
  psum (words_for letters g).nonempty ¬(words_for letters g).nonempty :=
dite (words_for letters g).nonempty (λ h, psum.inl h) (λ h, psum.inr h)

def geod_for' (g : G) := geod_for_helper letters g (get_emp letters g)


def word_length  (g : G) : enat :=
option.elim (geod_for' letters g) ⊤ (λ w, len (w : free_group ι))

notation `|`g`|` := word_length g





lemma word_length_realized (g : G) (w : free_group ι) (win : w ∈ words_for letters g):
  ∃ u ∈ geods_for letters g, | g | = len u :=
begin
  rcases get_emp letters g with (nonempty|empty),
  {
    -- Confusion here
    sorry
  },
  {
    exfalso,
    -- seems overly convoluted
    exact (eq_empty_iff_forall_not_mem.mp $ not_nonempty_iff_eq_empty.mp empty) w win,}

end

lemma word_length_le_word (g : G) (w : free_group ι) (win : w ∈ words_for letters g) :
  word_length letters g ≤ len (w : free_group ι) :=
begin
  rcases word_length_realized letters g w win with ⟨f,⟨word,geod⟩,exact⟩,
  calc word_length letters g = len f : exact
                         ... ≤ len (w : free_group ι) : enat.coe_le_coe.mpr $ ge.le $ geod w win,
end

lemma word_length_top_iff_no_words (g : G) :
  word_length letters g = ⊤ ↔ words_for letters g = ∅ :=
sorry
lemma word_length_fin_iff_words (g : G) :
  word_length letters g < ⊤ ↔ words_for letters g ≠ ∅ :=
sorry

def wl_neutral : word_length letters (1:G) = 0 :=
begin
  let emptyword := (1:free_group ι),
  have mapsto : val letters emptyword = (1:G), by sorry,
  have lengthz : len emptyword = 0, by simpa,
  let lol := word_length_le_word letters (1:G) emptyword mapsto,
  exact le_zero_iff.mp (calc word_length letters (1:G) ≤ len emptyword : lol
                                                        = 0 : sorry)
end

def wl_neutral' : word_length letters (1:G) = (0:enat) :=
let
  emptyword                                 := (1:free_group ι)
, mapsto    : val letters emptyword = (1:G) := by sorry
, lengthz   : len emptyword = 0             := by simpa
, lengthz'  : ↑(len emptyword) = (0:enat)   := by simpa
, lol : word_length letters (1:G) ≤ len emptyword := word_length_le_word letters (1:G) emptyword mapsto
, lol2 : word_length letters (1:G) ≤ (0:enat) := lengthz' ▸ lol
--, lol3 :word_length letters (1:G) = 0 := by simpa
in
  eq_zero_iff_le lol2


def wl_symm {g : G} : word_length letters (g⁻¹) = word_length letters g :=
begin

end

def wl_edist (g h : G) : enat := word_length letters (g * h⁻¹)

def wl_edist_self (g : G) : wl_edist letters g g = 0 :=
begin
  let lol := word_length_realized
end

end word_metric
