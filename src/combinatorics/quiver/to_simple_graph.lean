/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import combinatorics.quiver.basic
import combinatorics.simple_graph.basic
import combinatorics.quiver.connected_component
import combinatorics.simple_graph.connectivity

open function

universes u v w

namespace quiver


def to_simple_graph (V : Type*) [quiver V] : simple_graph V :=
simple_graph.from_rel (λ X Y, nonempty (X ⟶ Y))

namespace to_simple_graph

variables (V : Type*) [quiver.{u+1} V]

lemma adj_iff {X Y : V} :
  (to_simple_graph V).adj X Y ↔ X ≠ Y ∧ (nonempty (X ⟶ Y) ∨ nonempty (Y ⟶ X)) := iff.rfl

lemma zigzag_iff_reachable {X Y : V} :
  (zigzag_setoid V).r X Y ↔ (to_simple_graph V).reachable X Y :=
begin
  split,
  { rintro ⟨XY⟩,
    induction XY with Z Y XZ ZY ihXZ,
    { refl, },
    { apply simple_graph.reachable.trans ihXZ _,
      by_cases h : Z = Y,
      { rw h, },
      { apply simple_graph.adj.reachable,
        simp [adj_iff, h],
        cases ZY,
        exact or.inl (nonempty.intro ZY),
        exact or.inr (nonempty.intro ZY), } }, },
  { rintro ⟨XY⟩,
    induction XY,
    { apply setoid.refl', },
    { apply setoid.trans' _ _ XY_ih,
      simp [adj_iff] at XY_h,
      rcases XY_h with ⟨_,(⟨⟨XY⟩⟩|⟨⟨YX⟩⟩)⟩; constructor,
      exact XY.to_pos.to_path,
      exact YX.to_neg.to_path, } }
end

end to_simple_graph

end quiver
