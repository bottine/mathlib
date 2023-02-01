import combinatorics.simple_graph.ends.defs
import combinatorics.simple_graph.ends.cofinite
import data.enat.basic
import tactic.basic

universes u v w

variables {V V' V'' : Type u} (G : simple_graph V) (G' : simple_graph V') (G'' : simple_graph V'')

open simple_graph

-- TODO Implement these and put them in a correct file
constant simple_graph.edist (G : simple_graph V) : V → V → ℕ∞
constant simple_graph.edist_triangle (u v w : V) : G.edist u v ≤ G.edist u w + G.edist w v
constant simple_graph.edist_hom (φ : G →g G') : ∀ x y : V, G'.edist (φ x) (φ y) ≤ G.edist x y
constant simple_graph.reachable_iff_edist_lt_top (u v : V) : G.reachable u v ↔ G.edist u v < ⊤

@[reducible]
def coarse_lipschitz_with (K : ℕ∞) (C : ℕ) (f : V → V') :=
  ∀ ⦃x y : V⦄, ∀ a : ℕ∞, G.edist x y < a → G'.edist (f x) (f y) < K * a + C

def coarse_equal_with (K : ℕ∞) (f g : V → V'):=
  ∀ x : V, G'.edist (f x) (g x) < K

namespace coarse_lipschitz

variables {G} {G'}

-- can be derived from `hom`
protected theorem id : coarse_lipschitz_with G G 1 0 id := by {
  simp [coarse_lipschitz_with],
}

theorem hom (φ : G →g G') : coarse_lipschitz_with G G' 1 0 φ := by {
  intro,
  simp [coarse_lipschitz_with, simple_graph.edist_hom],
  sorry, -- transitivity
}

theorem mono {f : V → V'} {K K' : ℕ∞} {C C' : ℕ} (hK : K ≤ K') (hC : C ≤ C')
  (hf : coarse_lipschitz_with G G' K C f)
  : coarse_lipschitz_with G G' K' C' f := by {
    rw [coarse_lipschitz_with],
    intros x y a hdist,
    have := hf a hdist,
    sorry -- should follow from transitivity
  }

theorem comp (f : V → V') (g : V' → V'')
  {K K' : ℕ∞} {C C' : ℕ}
  (hf : coarse_lipschitz_with G G' K C f) (hg : coarse_lipschitz_with G' G'' K' C' g)
  : coarse_lipschitz_with G G'' (K * K') (K'.to_nat * C + C') (g ∘ f) := by {
    sorry
  }

theorem infty_wlog {P : (V → V') → Sort*} (C : ℕ) :
  ∀ (f : V → V') (K : ℕ∞) (hf : coarse_lipschitz_with G G' K C f), P f ↔
  ∀ (f : V → V') (hf : coarse_lipschitz_with G G' ⊤ C f), P f := sorry

theorem infty_iff (f : V → V') {C : ℕ} :
  (coarse_lipschitz_with G G' ⊤ C f) ↔ (∀ x y : V, G.reachable x y → G'.reachable (f x) (f y)) := by {
    have : ∀ (K : ℕ∞) (n : ℕ), ⊤ * K + n = ⊤ := by {
      intros K n,
      sorry -- needs missing `enat` lemmas
      },
    simp_rw [simple_graph.reachable_iff_edist_lt_top,
      coarse_lipschitz_with, this],
    sorry -- should be easy enough from here
  }

def out_restrict {f : V → V'} {k : ℕ∞} {c : ℕ} (hf : coarse_lipschitz_with G G' k c f) (K : set V) :
  coarse_lipschitz_with (G.out K) G' k c (f ∘ subtype.val) := by {
    intros x y a h,
    apply hf,
    sorry, -- can be proved using the fact that `subtype.val` is a homomorphism
  }

-- the "relative" version of `out`
def out'_restrict {K K' : set V} (h : K ⊆ K') {f : ↥(K)ᶜ → V'} {k : ℕ∞} {c : ℕ}
  (hf : coarse_lipschitz_with (G.out K) G' k c f) :
    coarse_lipschitz_with (G.out K') G' k c (f ∘ (simple_graph.out_hom G h).to_fun) := by {
      intros x y a h,
      apply hf,
      sorry -- should follow from transitivity
    }

def expand_out {L L' : set V'} (h : L ⊆ L') {f : V → ↥L'ᶜ} {k : ℕ∞} {c : ℕ}
  (hf : coarse_lipschitz_with G (G'.out L') k c f) :
  coarse_lipschitz_with G (G'.out L) k c ((induce_out id h) ∘ f) :=
  -- TODO maybe replace `induce_out id h`
    by {
      intros _ _ a h,
      have := hf a h,
      sorry, -- will follow from the fact that `induce_out id h` is a homomorphism
    }

def comp_map {f : V → V'} {k : ℕ∞} {c : ℕ} (hf : coarse_lipschitz_with G G' k c f) :
  G.connected_component → G'.connected_component :=
    simple_graph.connected_component.lift (λ v, G'.connected_component_mk (f v)) (by {
      intros _ _ p _,
      rw simple_graph.connected_component.eq,
      apply (infty_iff f).mp,
      apply mono le_top (nat.le_refl c) hf,
      exact nonempty.intro p, })

-- this could potentially be stated better using an "absolute" rather than a "relative" perspective
theorem up_comp {K K' : set V} (h : K ⊆ K') {f : ↥(K)ᶜ → V'} {k : ℕ∞} {c : ℕ}
  (hf : coarse_lipschitz_with (G.out K) G' k c f) (C : G.comp_out K') :
    comp_map hf (C.hom h) = comp_map (out'_restrict h hf) C := by {
      refine C.ind _,
      intros _ _,
      dsimp [comp_out.hom, connected_component.map, comp_map],
      congr, }

theorem comp_down {L L' : finset V'} (h : L ⊆ L') {f : V → ↥(↑L')ᶜ} {k : ℕ∞} {c : ℕ}
  (hf : coarse_lipschitz_with G (G'.out L') k c f) {C : G.connected_component} :
    comp_out.hom h (comp_map hf C) = (comp_map (expand_out h hf) C) := by {
      refine C.ind _,
      intro _,
      dsimp [comp_out.hom, connected_component.map, comp_map],
      congr,
      apply subtype.eq,
      simp, }

end coarse_lipschitz

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

-- TODO Move this to `defs`
lemma end_back {K K' : (finset V)ᵒᵖ} (h : K.unop ⊆ K'.unop) (e : G.end) :
  e.val K = (e.val K').hom h := by {
    symmetry,
    exact e.property (category_theory.op_hom_of_le h),  }

def coarse_map.end_map [decidable_eq V] {f : V → V'} (fcoarse : coarse_map G G' f) : G.end → G'.end := by
  {
    rintro e,
    refine ⟨λ L, _, _⟩,
    let comp_map := coarse_lipschitz.comp_map (fcoarse.induced_coarse_lipschitz L.unop),
    apply comp_map,
    let Gcomp := e.val (opposite.op $ fcoarse.finset_mapping L.unop),
    exact Gcomp,
    { intros L L' hLL',
      let K : (finset V)ᵒᵖ := opposite.op (
        (fcoarse.finset_mapping L.unop) ∪ (fcoarse.finset_mapping L'.unop)),
      have hL : (opposite.op $ fcoarse.finset_mapping L.unop).unop ⊆ K.unop := by {
        simp only [opposite.unop_op], apply finset.subset_union_left, },
      have hL' : (opposite.op $ fcoarse.finset_mapping L'.unop).unop ⊆ K.unop := by {
        simp only [opposite.unop_op], apply finset.subset_union_right, },
      dsimp,
      rw [← subtype.val_eq_coe,
      end_back hL e, end_back hL' e,
      coarse_lipschitz.up_comp, coarse_lipschitz.up_comp],
      dsimp [comp_out_functor],
      rw [coarse_lipschitz.comp_down],
      refl,
    },
  }

def coarse_equal.end_equal [decidable_eq V] {f g : V → V'} {k : ℕ∞}
  (fcoarse : coarse_map G G' f) (gcoarse : coarse_map G G' g)
  (close : coarse_equal_with G' k f g) :
  coarse_map.end_map fcoarse = coarse_map.end_map gcoarse := by {
    dsimp [coarse_map.end_map],
    ext e L,
    dsimp,
    let K : (finset V)ᵒᵖ := opposite.op (
        (fcoarse.finset_mapping L.unop) ∪ (gcoarse.finset_mapping L.unop)),
    have hfL : (opposite.op $ fcoarse.finset_mapping L.unop).unop ⊆ K.unop := sorry,
    have hgL : (opposite.op $ gcoarse.finset_mapping L.unop).unop ⊆ K.unop := sorry,
    rw [← subtype.val_eq_coe,
    end_back hfL e, end_back hgL e,
    coarse_lipschitz.up_comp, coarse_lipschitz.up_comp],

    generalize : e.val K = C,
    refine C.ind _,
    intros v hv,
    dsimp [coarse_lipschitz.comp_map],
    rw [simple_graph.connected_component.eq, simple_graph.reachable_iff_edist_lt_top],
    dsimp [induce_out],
    have := close v,
    sorry, -- need `coarse_close`, not just `coarse_equal`
  }
