import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition
import category_theory.functor.basic

open function
open finset
open set
open classical
open simple_graph.walk
open relation

universes u v w



noncomputable theory

--local attribute [instance] prop_decidable

namespace simple_graph


variables  {V : Type u}
           (G : simple_graph V)

section ends

def conn_comp_outside (s : finset V) : Type u :=
((⊤ : G.subgraph).delete_verts s).coe.connected_component

lemma conn_comp_outside.finite [locally_finite G] [preconnected G] (s : finset V) :
  fintype (conn_comp_outside G s) := sorry

lemma conn_comp_outside.nonempty  [locally_finite G] [preconnected G] (Ginf : (@set.univ V).infinite) (s : finset V) :
  nonempty (conn_comp_outside G s) := sorry

def conn_comp_outside.to_set (s : finset V) (c : conn_comp_outside G s) : set V :=
  { v : V | ∃ (p:v ∉ s), ((⊤ : G.subgraph).delete_verts s).coe.connected_component_mk (⟨v,by {simp,exact p}⟩) = c }

lemma conn_comp_outside_back_unique {s t : finset V} (h : s ⊆ t) :
∀ c : conn_comp_outside G t,
  ∃! d : conn_comp_outside G s,
    (conn_comp_outside.to_set G t c) ⊆ (conn_comp_outside.to_set G s d) := sorry

def conn_comp_outside_back {s t : finset V} (h : s ⊆ t) (c : conn_comp_outside G t) : conn_comp_outside G s :=
  classical.some (exists_of_exists_unique (conn_comp_outside_back_unique G h c))

def conn_comp_outside_back.iff {s t : finset V} (h : s ⊆ t) (c : conn_comp_outside G t) (d : conn_comp_outside G s):
  conn_comp_outside_back G h c = d ↔ (conn_comp_outside.to_set G t c) ⊆ (conn_comp_outside.to_set G s d) :=
begin
  split,
  { rintro equ, induction equ, exact (exists_of_exists_unique (conn_comp_outside_back_unique G h c)).some_spec},
  { exact unique_of_exists_unique (conn_comp_outside_back_unique G h c) (exists_of_exists_unique (conn_comp_outside_back_unique G h c)).some_spec},
end

lemma conn_comp_outside_back.refl (s : finset V) (c : conn_comp_outside G s) :
  conn_comp_outside_back G (finset.subset.refl s) c = c :=
unique_of_exists_unique
  (conn_comp_outside_back_unique G (finset.subset.refl s) c)
  (classical.some_spec (exists_of_exists_unique (conn_comp_outside_back_unique G (finset.subset.refl s) c)))
  (set.subset.refl (conn_comp_outside.to_set G s c))

lemma conn_comp_outside_back.comm  {r s t : finset V} (k : r ⊆ s) (h : s ⊆ t) (c : conn_comp_outside G t) :
  conn_comp_outside_back G k (conn_comp_outside_back G h c) = conn_comp_outside_back G (k.trans h) c :=
unique_of_exists_unique
  (conn_comp_outside_back_unique G (k.trans h) c)
  ((exists_of_exists_unique (conn_comp_outside_back_unique G h c)).some_spec.trans
     (exists_of_exists_unique (conn_comp_outside_back_unique G k (conn_comp_outside_back G h c))).some_spec)
  (classical.some_spec (exists_of_exists_unique (conn_comp_outside_back_unique G (k.trans h) c)))




-- def ends_system := category_theory.functor.mk (conn_comp_outside G) (conn_comp_outside_back G)


end ends

end simple_graph
