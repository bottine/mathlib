import combinatorics.simple_graph.ends.defs
import combinatorics.simple_graph.ends.cofinite
import data.enat.basic
import tactic.basic

universes u v w

-- TODO Implement these and put them in a correct file
constant simple_graph.edist {V : Type*} (G : simple_graph V) (u v : V) : ℕ∞
constant simple_graph.dist_triangle {V : Type*} (G : simple_graph V) (u v w : V) :
  G.edist u v ≤ G.edist u w + G.edist w v

variables {V V' : Type u} (G : simple_graph V) (G' : simple_graph V')

@[reducible]
def coarse_lipschitz_with (K : ℕ∞) (C : ℕ) (f : V → V') :=
  ∀ x y : V, G'.edist (f x) (f y) < K * G.edist x y + C

def coarse_equal_with (K : ℕ∞) (f g : V → V'):=
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

theorem lipschitz_up (f : V → V') {K K' : ℕ∞} {C C' : ℕ} (hK : K ≤ K') (hC : C ≤ C')
  (hf : coarse_lipschitz_with G G' K C f)
  : coarse_lipschitz_with G G' K' C' f := by {
    rw [coarse_lipschitz_with],
    intros x y,
    apply lt_trans,
    { apply hf, },
    sorry -- needs work with `enat`
  }

theorem lipschitz_infty_wlog {P : (V → V') → Sort*} (C : ℕ) :
  ∀ (f : V → V') (K : ℕ∞) (hf : coarse_lipschitz_with G G' K C f), P f ↔
  ∀ (f : V → V') (hf : coarse_lipschitz_with G G' ⊤ C f), P f := sorry

theorem lipschitz_infty_iff (f : V → V') (C : ℕ) (hf : coarse_lipschitz_with G G' ⊤ C f) :
  ∀ x y : V, G.reachable x y → G'.reachable (f x) (f y) := sorry

def lipschitz_comp_map (f : V → V') (K : ℕ∞) (C : ℕ) (hf : coarse_lipschitz_with G G' K C f) :
  G.connected_component → G'.connected_component := sorry

end lipschitz

-- set_option trace.class_instances true

/-- The kind of map between graphs which induces a map on the ends. -/
structure coarse_map {V V' : Type u} (G : simple_graph V) (G' : simple_graph V') (φ : V → V') :=
  (κ : ℕ∞) (C : ℕ)
  (finset_mapping : finset V' → finset V)
  (finset_inv_sub : ∀ L : finset V', φ ⁻¹' (L : set V') ⊆ (finset_mapping L : set V))
  (induced_coarse_lipschitz : ∀ L : finset V',
    coarse_lipschitz_with (G.out $ finset_mapping L) (G'.out L)
      κ C (induce_out φ (finset_inv_sub L)))

def coarse_map.end_map {f : V → V'} (fcoarse : coarse_map G G' f) : G.end → G'.end := sorry

def coarse_equal.end_equal (f g : V → V') (K : ℕ∞) (fcoarse : coarse_map G G' f) (gcoarse : coarse_map G G' g)
  (close : coarse_equal_with G' K f g) : coarse_map.end_map G G' fcoarse = coarse_map.end_map G G' gcoarse := sorry
