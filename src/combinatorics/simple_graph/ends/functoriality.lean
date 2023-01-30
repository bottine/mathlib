import combinatorics.simple_graph.ends.defs
import combinatorics.simple_graph.ends.cofinite
import data.enat.basic
import tactic.basic

universes u v w

variables {V V' V'' : Type u} (G : simple_graph V) (G' : simple_graph V') (G'' : simple_graph V'')

-- TODO Implement these and put them in a correct file
constant simple_graph.edist {V : Type*} (G : simple_graph V) (u v : V) : ℕ∞
constant simple_graph.dist_triangle {V : Type*} (G : simple_graph V) (u v w : V) :
  G.edist u v ≤ G.edist u w + G.edist w v
constant simple_graph.edist_hom (φ : G →g G') :  ∀ x y : V, G'.edist (φ x) (φ y) = G.edist x y
constant simple_graph.reachable_iff_edist_lt_top {V : Type*} (G : simple_graph V) (u v : V) :
  G.reachable u v ↔ G.edist u v < ⊤

@[reducible]
def coarse_lipschitz_with (K : ℕ∞) (C : ℕ) (f : V → V') :=
  ∀ x y : V, ∀ a : ℕ∞, G.edist x y < a → G'.edist (f x) (f y) < K * a + C

def coarse_equal_with (K : ℕ∞) (f g : V → V'):=
  ∀ x : V, G'.edist (f x) (g x) < K

section lipschitz

variables {G} {G'}

-- can be derived from `lipschitz_hom`
theorem lipschitz_id : coarse_lipschitz_with G G 1 0 id := by {
  simp [coarse_lipschitz_with],
}

theorem lipschitz_hom (φ : G →g G') : coarse_lipschitz_with G G' 1 0 φ := by {
  simp [coarse_lipschitz_with, simple_graph.edist_hom],
}

theorem lipschitz_up {f : V → V'} {K K' : ℕ∞} {C C' : ℕ} (hK : K ≤ K') (hC : C ≤ C')
  (hf : coarse_lipschitz_with G G' K C f)
  : coarse_lipschitz_with G G' K' C' f := by {
    rw [coarse_lipschitz_with],
    intros x y a hdist,
    sorry -- should follow from transitivity
  }

theorem lipschitz_comp (f : V → V') (g : V' → V'')
  {K K' : ℕ∞} {C C' : ℕ}
  (hf : coarse_lipschitz_with G G' K C f) (hg : coarse_lipschitz_with G' G'' K' C' g)
  : coarse_lipschitz_with G G'' (K * K') (C + C') (g ∘ f) := sorry
  -- TODO work out the exact additive constant; it may have to be `ℕ∞` instead of `ℕ`

theorem lipschitz_infty_wlog {P : (V → V') → Sort*} (C : ℕ) :
  ∀ (f : V → V') (K : ℕ∞) (hf : coarse_lipschitz_with G G' K C f), P f ↔
  ∀ (f : V → V') (hf : coarse_lipschitz_with G G' ⊤ C f), P f := sorry

theorem lipschitz_infty_iff (f : V → V') {C : ℕ} :
  (coarse_lipschitz_with G G' ⊤ C f) ↔ (∀ x y : V, G.reachable x y → G'.reachable (f x) (f y)) := by {
    have : ∀ (K : ℕ∞) (n : ℕ), ⊤ * K + n = ⊤ := by {
      intros K n,
      sorry -- needs missing `enat` lemmas
      },
    simp_rw [simple_graph.reachable_iff_edist_lt_top,
      coarse_lipschitz_with, this],
    sorry -- should be easy enough from here
  }

def lipschitz_comp_map {f : V → V'} {K : ℕ∞} {C : ℕ} (hf : coarse_lipschitz_with G G' K C f) :
  G.connected_component → G'.connected_component :=
    simple_graph.connected_component.lift (λ v, G'.connected_component_mk (f v)) (by {
      intros _ _ p _,
      rw simple_graph.connected_component.eq,
      apply (lipschitz_infty_iff f).mp,
      apply lipschitz_up le_top (nat.le_refl C) hf,
      exact nonempty.intro p, })

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

variables {G} {G'}

def coarse_map.end_map {f : V → V'} (fcoarse : coarse_map G G' f) : G.end → G'.end := by
  {
    rintro ⟨Gsec, Gend⟩,
    refine ⟨λ L, _, _⟩,
    let comp_map := lipschitz_comp_map (fcoarse.induced_coarse_lipschitz L.unop),
    apply comp_map,
    let Gcomp := Gsec (opposite.op $ fcoarse.finset_mapping (opposite.unop L)),
    exact Gcomp,
    {
      intros L L' hLL',
      dsimp,
      apply simple_graph.connected_component.ind₂,
      sorry,
    },
  }

def coarse_equal.end_equal (f g : V → V') (K : ℕ∞) (fcoarse : coarse_map G G' f) (gcoarse : coarse_map G G' g)
  (close : coarse_equal_with G' K f g) : coarse_map.end_map fcoarse = coarse_map.end_map gcoarse := sorry
