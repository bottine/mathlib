/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import measure_theory.measure.lebesgue
import analysis.calculus.monotone
import analysis.bounded_variation
import tactic.swap_var

open_locale big_operators nnreal ennreal
open set measure_theory

variables {α β : Type*} [linear_order α] [linear_order β]
{E F : Type*} [pseudo_emetric_space E] [pseudo_emetric_space F]
{V : Type*} [normed_add_comm_group V] [normed_space ℝ V] [finite_dimensional ℝ V]


namespace evariation_on

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
  apply le_antisymm,
  work_on_goal 2 { swap_var f ↔ f', replace h := h.symm, },
  all_goals
  { apply supr_le _,
    rintros ⟨n, ⟨u, hu, us⟩⟩,
    simp,
    have : ∑ (x : ℕ) in finset.range n, edist (f (u (x + 1))) (f (u x)) =
           ∑ (x : ℕ) in finset.range n, edist (f' (u (x + 1))) (f' (u x)), by
    { congr, funext n, congr; apply h (us $ _), },
    rw this,
    apply le_supr (λ (p : ℕ × {u : ℕ → α // monotone u ∧ ∀ i, u i ∈ s}),
      ∑ i in finset.range p.1, edist (f' ((p.2 : ℕ → α) (i+1))) (f' ((p.2 : ℕ → α) i)))
      ⟨n, ⟨u, hu, us⟩⟩, },
end

lemma comp_eq (f : α → E) {s : set α} {t : set β} [nonempty β] (φ : β → α)
  (hφ : monotone_on φ t ) (φst : set.maps_to φ t s) (φsur : set.surj_on φ t s) :
  evariation_on (f∘φ) t = evariation_on f s :=
begin
  apply le_antisymm (comp_mono f φ hφ φst),

  let ψ := φ.inv_fun_on t,
  have ψφs : set.eq_on (φ∘ψ) id s := φsur.right_inv_on_inv_fun_on,
  have ψts : set.maps_to ψ s t := φsur.maps_to_inv_fun_on,
  have hψ : monotone_on ψ s, by
  { rintro x xs y ys l,
    rcases  le_total (ψ x) (ψ y) with (ψxy|ψyx),
    { exact ψxy, },
    { let := hφ (ψts ys) (ψts xs) ψyx,
      simp only [←function.comp_app φ ψ] at this,
      rw [ψφs xs,ψφs ys] at this,
      cases le_antisymm l this,
      refl, }, },

  change evariation_on (f∘id) s ≤ evariation_on (f ∘ φ) t,
  rw ←eq_of_eq_on (ψφs.comp_left : set.eq_on (f ∘ (φ∘ψ)) (f ∘ id) s),
  apply comp_mono _ ψ hψ ψts,
end

end evariation_on


section arc_length_parameterization

variables {I : set ℝ} (hI : ∀ (a b c : ℝ), a ≤ c → c ≤ b → a ∈ I → b ∈ I → c ∈ I) (f : I → E)

noncomputable def arc_length (x₀ : ℝ) (x : ℝ) : ereal :=
if x₀ ≤ x then
  evariation_on f {y : I | y.val ∈ Icc x₀ x}
else
  - evariation_on f {y : I | y.val ∈ Icc x x₀}

lemma arc_length_monotone (x₀ : ℝ) : monotone (arc_length f x₀) := sorry

end arc_length_parameterization
