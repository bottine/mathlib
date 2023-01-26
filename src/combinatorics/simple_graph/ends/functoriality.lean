import combinatorics.simple_graph.ends.defs
import combinatorics.simple_graph.ends.cofinite
import data.enat.basic
import tactic.basic

-- TODO Implement these and put them in a correct file
constant simple_graph.edist {V : Type*} (G : simple_graph V) (u v : V) : enat
constant simple_graph.dist_triangle {V : Type*} (G : simple_graph V) (u v w : V) :
  G.edist u v ≤ G.edist u w + G.edist w v

variables {V V' : Type*} (G : simple_graph V) (G' : simple_graph V')

@[reducible]
def coarse_lipschitz_with (K : enat) (C : nat) (f : V → V') :=
  ∀ x y : V, G'.edist (f x) (f y) < K * G.edist x y + C

def coarse_equal_with (f g : V → V') (K : enat) :=
  ∀ x : V, G'.edist (f x) (g x) < K

section lipschitz

-- can be derived from `lipschitz_hom`
theorem lipschitz_id : coarse_lipschitz_with G G 2 1 id := by {
  show ∀ x y, G.edist x y < 2 * G.edist x y + 1,
  sorry, -- this should be easy enough
}

theorem lipschitz_hom (φ : G →g G') : coarse_lipschitz_with G G' 2 1 φ := by {
  rw [coarse_lipschitz_with],
  intros x y,
  -- TODO Make this a property of `edist`
  have : ∀ x y : V, G'.edist (φ x) (φ y) = G.edist x y := sorry,
  rw [this],
  sorry, -- another easy goal
}

theorem lipschitz_up (f : V → V') {K K' : enat} {C C' : nat} (hK : K ≤ K') (hC : C ≤ C')
  (hf : coarse_lipschitz_with G G' K C f)
  : coarse_lipschitz_with G G' K' C' f := by {
    rw [coarse_lipschitz_with],
    intros x y,
    apply lt_trans,
    { apply hf, },
    sorry -- needs work with `enat`
  }

end lipschitz

/-- The kind of map between graphs which induces a map on the ends. -/
structure coarse_map (G : simple_graph V) (G' : simple_graph V') (φ : V → V') :=
  (κ : enat) (C : nat)
  (finset_mapping : finset V' → finset V)
  (finset_inv_sub : ∀ L : finset V', (↑φ : V → V')⁻¹' ↑L ⊆ ↑(finset_mapping L))
  (induced_coarse_lipschitz : ∀ L : finset V',
    coarse_lipschitz_with (G.out $ finset_mapping L) (G'.out L)
      κ C (induce_out ↑φ (finset_inv_sub L)))
