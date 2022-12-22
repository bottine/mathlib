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

def length_metric (E : Type*) [pseudo_emetric_space E] := E

variables {E : Type*} [pseudo_emetric_space E]

def path.length {x y : E} (p : path x y) : ennreal :=
evariation_on p.to_fun (set.univ)

def of : E → length_metric E := id
def fo : length_metric E → E := id


instance : pseudo_emetric_space (length_metric E) :=
{ edist := λ x y, infi (λ (p : path (fo x) (fo y)), p.length),
  edist_self := by
  { rintro x,
    dsimp [edist],
    change infi path.length = ⊥,
    rw infi_eq_bot, rintro b hb, use path.refl x,
    dsimp [path.length],
    have : evariation_on ⇑(path.refl (fo x)) set.univ = 0, by
    { apply evariation_on.subsingleton, },
     },
  edist_comm := sorry,
  edist_triangle := sorry
}
