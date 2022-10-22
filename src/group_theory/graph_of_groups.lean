/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Joachim Breitner
-/
import algebra.free_monoid.basic
import group_theory.congruence
import group_theory.is_free_group
import group_theory.subgroup.pointwise
import data.list.chain
import set_theory.cardinal.ordinal
import combinatorics.quiver.basic
import category_theory.groupoid.presentation
import category_theory.groupoid.free_groupoid

open set

universes u v w

structure graph_of_groups (V : Type*) extends (quiver.{v+1} V) :=
( vertex_group : V → Type u )
( vertex_group_group : Π (x : V), group (vertex_group x) )
( edge_group : Π {x y : V}, (x ⟶ y) → Type u )
( edge_group_group : Π {x y : V} (e : x ⟶ y), group (edge_group e) )
( ι : Π {x y : V} (e : x ⟶ y), edge_group e →* vertex_group x )
( τ : Π {x y : V} (e : x ⟶ y), edge_group e →* vertex_group y )
( ι_inj : Π {x y : V} (e : x ⟶ y), function.injective $ ι e )
( τ_inj   : Π {x y : V} (e : x ⟶ y), function.injective $ τ e )


variables {V : Type*} [decidable_eq V]  (G : graph_of_groups V)

def fundamental_groupoid_gen  (G : graph_of_groups V) := V

instance fundamental_groupoid_gen_quiver : quiver (fundamental_groupoid_gen G) :=
⟨ λ x y, (G.to_quiver.hom x y) ⊕ (if x = y then G.vertex_group x else pempty) ⟩


def fundemantal_groupoid_relations :
  ∀ (x y : category_theory.free_groupoid (fundamental_groupoid_gen G)), set $ x ⟶ y := sorry
/-
Given `x y`,

* If `x = y`, then
  * all `[g,h,(g*h)⁻¹]` for all `g h` in `vertex_group_carrier x`
  * `[1]` when `1` in `vertex_group_carrier x` (probably follows from the above)
  * `[g,g⁻¹]` for all `g` in `vertex_group_carrier x` (probably follows from the above)
* For all `e : x ⟶ y` and all `g` in edge_group_group `[y',ι_e g,y] = [τ_e g]` where `ι_e τ_e` are
  `ι e` and `τ   respectively, and `y'` is the formal inverse of `y` in the free
  groupoid.

-/
