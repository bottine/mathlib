/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.subgraph
import combinatorics.simple_graph.connectivity
import data.list

open function

universes u v w

namespace simple_graph

section defs

variables (X : Type*) {M : Type*} [has_smul M X] (S : set M)

inductive cayley_graph.adj_gen : X → X → Prop
| mk (m : S) (x : X) : cayley_graph.adj_gen (x) (m.val • x)


lemma cayley_graph.adj_gen_iff {x y : X} : cayley_graph.adj_gen X S x y ↔ ∃ (m : S), y = m.val • x :=
begin
  split,
  { rintro ⟨m,x⟩, exact ⟨m,rfl⟩, },
  { rintro ⟨m,rfl⟩, constructor, },
end

def cayley_graph : simple_graph X := simple_graph.from_rel (cayley_graph.adj_gen X S)

end defs

namespace cayley_graph

variables {X : Type*} {M : Type*} [has_smul M X] (S : set M)

lemma mono {S} {T : set M} (h : S ≤ T) : cayley_graph X S ≤ cayley_graph X T :=
begin
  apply simple_graph.from_rel_mono,
  rintros _ _ ⟨⟨m,mS⟩,x⟩,
  exact adj_gen.mk ⟨m, h mS⟩ x,
end

lemma adj_iff {x y : X} : (cayley_graph X S).adj x y ↔ (x ≠ y ∧ ∃ m ∈ S, m • x = y ∨ m • y = x) :=
begin
  simp only [cayley_graph, adj_gen_iff, from_rel_adj, ne.def, set_coe.exists],
  congr', ext, split,
  { rintros (⟨m,h,rfl⟩|⟨m,h,rfl⟩), exact ⟨m,h,or.inl rfl⟩, exact ⟨m,h,or.inr rfl⟩, },
  { rintros ⟨m,h,(rfl|rfl)⟩, exact or.inl ⟨m,h,rfl⟩, exact or.inr ⟨m,h,rfl⟩, },
end

lemma neighbor_set_eq {x : X} :
  (cayley_graph X S).neighbor_set x = {y | x ≠ y ∧ ∃ m ∈ S, m • x = y ∨ m • y = x} :=
by { dsimp [neighbor_set, set_of], ext, rw adj_iff, }

lemma neighbor_set_eq' {x : X} :
  (cayley_graph X S).neighbor_set x
= {y | x ≠ y} ∩ ({y | ∃ m ∈ S, m • x = y} ∪ {y | ∃ m ∈ S,m • y = x}) :=
begin
  simp only [cayley_graph, ne.def, exists_prop], ext,
  simp only [mem_neighbor_set, set.mem_inter_iff, set.mem_set_of_eq, set.mem_union,
             simple_graph.from_rel_adj, adj_gen_iff, ne.def, set_coe.exists, exists_prop,
             and.congr_right_iff],
  rintro, congr'; ext; tauto,
end

end cayley_graph

end simple_graph
