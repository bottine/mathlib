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
import group_theory.complement

open set category_theory

universes u v w

structure graph_of_groups (V : Type*) extends (quiver.{v+1} V) :=
( vG : V → Type u )
( vG_group : Π (x : V), group (vG x) )
( eG : Π {x y : V}, (x ⟶ y) → Type u )
( eG_group : Π {x y : V} (e : x ⟶ y), group (eG e) )
( ι : Π {x y : V} (e : x ⟶ y), eG e →* vG x )
( τ : Π {x y : V} (e : x ⟶ y), eG e →* vG y )
( ι_inj : Π {x y : V} (e : x ⟶ y), function.injective $ ι e )
( τ_inj   : Π {x y : V} (e : x ⟶ y), function.injective $ τ e )


variables {V : Type*} [decidable_eq V] (G : graph_of_groups V)

instance Vquiver : quiver V := G.to_quiver
instance (x : V) : group (G.vG x) := G.vG_group x
instance {x y : V} (e : G.hom x y) : group (G.eG e) := G.eG_group e

def π₁_gen  (G : graph_of_groups V) := V

instance π₁_gen_quiver : quiver (π₁_gen G) :=
⟨ λ x y, (G.hom x y) ⊕ (if x = y then G.vG x else pempty) ⟩

def ι_transversals := Π {x y : V} (e : G.hom x y), subgroup.left_transversals (range $ G.ι e)
def τ_transversals := Π {x y : V} (e : G.hom x y), subgroup.left_transversals (range $ G.τ e)


notation ` @. ` x :100 := @quiver.path.nil _ _ x
notation p ` :+ ` f :100 := p.cons f.to_pos
notation p ` :- ` f :100 := p.cons f.to_neg

def recast (x : V) : @free_groupoid V (π₁_gen_quiver G) :=
(groupoid.free.of _).obj x

set_option pp.universes

abbreviation rel.group_mul {x : V} (g h : G.vG x) : (recast G x) ⟶ (recast G x) :=
begin
  dsimp [quiver.hom],
  apply quot.mk,
  refine quiver.path.cons _ _,
end

def π₁_relations_vertex (x : V) : set $ (recast G x) ⟶ (recast G x) :=
set.image2
  ( λ (g h : G.vG x),
    @. (recast G x)
      :+ (sum.inr g)
      :+ (sum.inr h)
      :+ (sum.inr $ (g*h)⁻¹) ) (univ) (univ)

def fundemantal_groupoid_relations (x y : V) :
  set $ (recast G x) ⟶ (recast G y) := sorry


/-
Given `x y`,

* If `x = y`, then
  * all `[g,h,(g*h)⁻¹]` for all `g h` in `vertex_group_carrier x`
  * `[1]` when `1` in `vertex_group_carrier x` (probably follows from the above)
  * `[g,g⁻¹]` for all `g` in `vertex_group_carrier x` (probably follows from the above)
* For all `e : x ⟶ y` and all `g` in eG_group `[y',ι_e g,y] = [τ_e g]` where `ι_e τ_e` are
  `ι e` and `τ   respectively, and `y'` is the formal inverse of `y` in the free
  groupoid.

-/
