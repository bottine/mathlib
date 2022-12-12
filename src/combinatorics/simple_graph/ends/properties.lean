/-
Copyright (c) 2022 Anand Rao, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao, Rémi Bottinelli
-/
import combinatorics.simple_graph.ends.defs
/-!
# Properties of the ends of graphs

This file is meant to contain results about the ends of (locally finite connected) graphs.

-/

variables {V : Type} (G : simple_graph V)

namespace simple_graph

lemma ends_of_finite [finite V] : is_empty G.end :=
begin
  rw is_empty_iff,
  rintro ⟨s, sec⟩,
  let K : finset V := set.finite_univ.to_finset,
  obtain ⟨v, h⟩ := (s K).nempty,
  exact set.disjoint_iff.mp (s K).outside ⟨by simp only [set.finite.coe_to_finset], h⟩,
end

/--!

## Ends of locally finite, connected graphs

-/

instance comp_out_finite [locally_finite G] [Gc : connected G] :
  ∀ (K : finset V), finite (G.comp_out K) :=
begin
  rintro K,
  cases K.eq_empty_or_nonempty,
  { cases h, dsimp [comp_out, out],
    rw set.compl_empty,
    haveI : finite G.connected_component, by
    { apply @finite.of_subsingleton _ _,
      constructor,
      apply connected_component.ind₂,
      simp only [connected_component.eq],
      exact Gc.preconnected, },
    apply finite.of_equiv (G.connected_component),
    exact (connected_component.iso (induce_univ_iso G)).symm, },
  let touch : G.comp_out K → K, by
  { rintro C, obtain h := C.adj h, }
end

instance comp_out_nonempty_of_infinite [locally_finite G] [connected G] [infinite V] :
  ∀ (K : finset V), nonempty (G.comp_out K) :=
begin
  sorry,
end

-- `Gc` has to be fed explicitely; I don't know why
lemma nonempty_ends_of_infinite [Glf : locally_finite G] [Gc : connected G] [Vi : infinite V] :
  G.end.nonempty :=
@nonempty_sections_of_fintype_inverse_system' _ _ _ G.comp_out_functor
  (λ K, @fintype.of_finite _ $ @simple_graph.comp_out_finite V G _ Gc K)
  (@simple_graph.comp_out_nonempty_of_infinite V G _ Gc _)

end simple_graph
