import combinatorics.quiver.basic
import algebra.group.defs
import group_theory.group_action.basic
import group_theory.group_action.group
import group_theory.group_action.defs
import group_theory.subgroup.basic
import group_theory.coset
import group_theory.quotient_group
import group_theory.group_action.quotient
import combinatorics.quiver.symmetric
import combinatorics.quiver.reduced_path

open function

universes u v w

namespace quiver

variables {U : Type*} [quiver.{u+1} U]
          {V : Type*} [quiver.{v+1} V] (φ : U ⟶q V)
          {W : Type*} [quiver.{w+1} W] (ψ : V ⟶q W)

@[reducible] def star (u : U) := Σ (v : U), (u ⟶ v)
@[reducible] def costar (u : U) := Σ (v : U), (v ⟶ u)

@[simp] lemma star_eq_iff {u : U} (F G : star u) :
  F = G ↔ ∃ h : F.1 = G.1, (F.2).cast rfl h = G.2 :=
begin
  split,
  { rintro ⟨⟩, exact ⟨rfl,rfl⟩, },
  { induction F, induction G, rintro ⟨h,H⟩, cases h, cases H,
    simp only [eq_self_iff_true, heq_iff_eq, and_self], }
end

@[simp] lemma costar_eq_iff {u : U} (F G : costar u) :
  F = G ↔ ∃ h : F.1 = G.1, (F.2).cast h rfl = G.2 :=
begin
  split,
  { rintro ⟨⟩, exact ⟨rfl,rfl⟩, },
  { induction F, induction G, rintro ⟨h,H⟩, cases h, cases H,
    simp only [eq_self_iff_true, heq_iff_eq, and_self], }
end

@[simps] def prefunctor.star (u : U) : star u → star (φ.obj u) := λ F, ⟨(φ.obj F.1), φ.map F.2⟩
@[simps] def prefunctor.costar (u : U) : costar u → costar (φ.obj u) := λ F, ⟨(φ.obj F.1), φ.map F.2⟩

@[simp] lemma prefunctor.star_apply {u v : U} (e : u ⟶ v) :
  φ.star u ⟨v, e⟩ = ⟨φ.obj v, φ.map e⟩ := rfl
@[simp] lemma prefunctor.costar_apply {u v : U} (e : v ⟶ u) :
  φ.costar u ⟨v, e⟩ = ⟨φ.obj v, φ.map e⟩ := rfl

@[simp] lemma prefunctor.star_comp (u : U) :
  (φ ≫q ψ).star u = (ψ.star (φ.obj u)) ∘ ((φ.star) u) := rfl
@[simp] lemma prefunctor.costar_comp (u : U) :
  (φ ≫q ψ).costar u = (ψ.costar (φ.obj u)) ∘ ((φ.costar) u) := rfl

@[reducible]
def prefunctor.is_covering :=
  (∀ u, function.bijective (φ.star u)) ∧ (∀ u, function.bijective (φ.costar u))

@[simp]
lemma prefunctor.map_inj_of_is_covering (hφ : φ.is_covering) {u v : U} :
  function.injective (λ (f : u ⟶ v), φ.map f) :=
begin
  rintro f g he,
  have : φ.star u (⟨v,f⟩ : star u) = φ.star u (⟨v,g⟩ : star u), by
  { simp only [prefunctor.star, eq_self_iff_true, heq_iff_eq, true_and], exact he, },
  simpa only [eq_self_iff_true, heq_iff_eq, true_and] using (hφ.left u).left this,
end

lemma comp (hφ : φ.is_covering) (hψ : ψ.is_covering) :
  (φ ≫q ψ).is_covering :=
begin
  simp [prefunctor.is_covering],
  exact  ⟨λ u, function.bijective.comp (hψ.left _) (hφ.left u),
          λ u, function.bijective.comp (hψ.right _) (hφ.right u)⟩,
end
lemma comp' (hψ : ψ.is_covering) (hφψ : (φ ≫q ψ).is_covering ) : φ.is_covering :=
begin
  split;
  rintro u,
  { rw ←@function.bijective.of_comp_iff' _ _ _ (ψ.star $ φ.obj u) (hψ.left $ φ.obj u) (φ.star u),
    exact hφψ.left u},
  { rw ←@function.bijective.of_comp_iff' _ _ _ (ψ.costar $ φ.obj u) (hψ.right $ φ.obj u) (φ.costar u),
    exact hφψ.right u},
end
lemma comp'' (hφ : φ.is_covering) (hφψ : (φ ≫q ψ).is_covering) (φsur : function.surjective φ.obj) :
  ψ.is_covering :=
begin
  split;
  rintro v;
  obtain ⟨u,rfl⟩ := φsur v,
  { rw ←@function.bijective.of_comp_iff _ _ _ (ψ.star $ φ.obj u) (φ.star u)  (hφ.left u),
    exact hφψ.left u, },
  { rw ←@function.bijective.of_comp_iff _ _ _ (ψ.costar $ φ.obj u) (φ.costar u)  (hφ.right u),
    exact hφψ.right u, },
end

def symmetrify_star (u : U) : star (symmetrify.of.obj u) ≃ star u ⊕ costar u :=
begin
  fsplit,
  { rintro ⟨v,(f|g)⟩, exact sum.inl ⟨v,f⟩, exact sum.inr ⟨v,g⟩, },
  { rintro (⟨v,f⟩|⟨v,g⟩), exact ⟨v,f.to_pos⟩, exact ⟨v,g.to_neg⟩, },
  { rintro ⟨v,(f|g)⟩, simp, },
  { rintro (⟨v,f⟩|⟨v,g⟩), simp, },
end

@[simp] lemma symmetrify_star_lapply {u v : U} (e : u ⟶ v) :
  symmetrify_star u ⟨v, sum.inl e⟩ = sum.inl ⟨v, e⟩ := rfl
@[simp] lemma symmetrify_star_rapply {u v : U} (e : v ⟶ u) :
  symmetrify_star u ⟨v, sum.inr e⟩ = sum.inr ⟨v, e⟩ := rfl

@[simps]
def symmetrify_costar (u : U) : costar (symmetrify.of.obj u) ≃ costar u ⊕ star u :=
begin
  fsplit,
  { rintro ⟨v,(f|g)⟩, exact sum.inl ⟨v,f⟩, exact sum.inr ⟨v,g⟩, },
  { rintro (⟨v,f⟩|⟨v,g⟩), exact ⟨v,quiver.hom.to_pos f⟩, exact ⟨v,quiver.hom.to_neg g⟩, },
  { rintro ⟨v,(f|g)⟩, simp, },
  { rintro (⟨v,f⟩|⟨v,g⟩), simp, },
end

lemma prefunctor.symmetrify_star (u : U) : (φ.symmetrify.star u) =
 (symmetrify_star (φ.obj u)).symm ∘ (sum.map (φ.star u) (φ.costar u)) ∘ (symmetrify_star u) :=
begin
  rw equiv.eq_symm_comp,
  ext e', cases e' with v e, cases e;
  simp,
end

lemma prefunctor.symmetrify_costar (u : U) : (φ.symmetrify.costar u) =
 (symmetrify_costar (φ.obj u)).symm ∘ (sum.map (φ.costar u) (φ.star u)) ∘ (symmetrify_costar u) :=
begin
  rw equiv.eq_symm_comp,
  ext e, cases e with v e, cases e;
  simp,
end


lemma is_covering.symmetrify (hφ : φ.is_covering) : φ.symmetrify.is_covering :=
begin
  split;
  rintro u,
  { rw φ.symmetrify_star u,
    simp only [equiv_like.comp_bijective, equiv_like.bijective_comp],
    exact ⟨function.injective.sum_map (hφ.left u).left (hφ.right u).left,
         function.surjective.sum_map (hφ.left u).right (hφ.right u).right⟩, },
  { rw φ.symmetrify_costar u,
    simp only [equiv_like.comp_bijective, equiv_like.bijective_comp],
    exact ⟨function.injective.sum_map (hφ.right u).left (hφ.left u).left,
         function.surjective.sum_map (hφ.right u).right (hφ.left u).right⟩, },
end

lemma prefunctor.symmetrify_is_reduced_iff (hφ : φ.is_covering) :
  Π {u v : symmetrify U} (p : path u v),
  p.is_reduced ↔ (φ.symmetrify.map_path p).is_reduced
| _ _ (path.nil) := by simp only [path.nil_is_reduced, prefunctor.map_path_nil]
| _ _ (path.cons (path.nil) f) := by
  { change f.to_path.is_reduced ↔ (φ.symmetrify.map f).to_path.is_reduced,
    simp only [path.to_path_is_reduced], }
| u v (@path.cons _ _ _ z _ (@path.cons _ _ _ w _ p f) g) := by
  { have : (p.cons f).length < ((p.cons f).cons g).length, by { simp, },
    rw [prefunctor.map_path_cons, path.cons_cons_is_reduced,
        prefunctor.symmetrify_is_reduced_iff (p.cons f),
        prefunctor.map_path_cons, path.cons_cons_is_reduced],
    apply and_congr, refl,
    let F : costar _ := ⟨_,f⟩,
    let G : costar _ := ⟨_,reverse g⟩,
    have : reverse (φ.symmetrify.map g) = φ.symmetrify.map (reverse g), by { cases g; simp, },
    rw this, clear this,
    have : ∀ (F G : costar z), φ.symmetrify.costar _ F = φ.symmetrify.costar _ G ↔ F = G, by
    { rintro F G,
      exact ⟨λ e , ((is_covering.symmetrify φ hφ).right _).left e, λ e, by { cases e, refl, }⟩, },
    let := (@costar_eq_iff _ _ _ (φ.symmetrify.costar _ F) (φ.symmetrify.costar _ G)).symm.trans
              ((this F G).trans (@costar_eq_iff _ _ _ F G)),
    exact (iff.not this).symm, }
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf $ λ (P : Σ' (u v : symmetrify U), path u v), P.2.2.length⟩]}

/-
@[reducible] def path_star (u : U) := Σ v : U, path u v

@[simp] lemma path_star_eq_iff {u : U} (P Q : path_star u) :
  P = Q ↔ ∃ h : P.1 = Q.1, (P.2).cast rfl h = Q.2 :=
begin
  split,
  { rintro rfl, exact ⟨rfl,rfl⟩, },
  { rintro ⟨h,H⟩, induction P, induction Q, cases h, cases H, refl, }
end

def prefunctor.path_star (u : U) : path_star u → path_star (φ.obj u) :=
λ p, ⟨φ.obj p.1, φ.map_path p.2⟩

@[simp] lemma prefunctor.path_star_apply {u v : U} (p : path u v) :
  φ.path_star u ⟨v, p⟩ = ⟨φ.obj v, φ.map_path p⟩ := rfl

lemma prefunctor.path_star_bijective (hφ : φ.is_covering) (u : U) :
  function.bijective (φ.path_star u) :=
begin
  split,
  { rintro ⟨v₁, p₁⟩,
    induction p₁ with  x₁ y₁ p₁ e₁ ih;
    rintro ⟨y₂, p₂⟩; cases p₂ with x₂ _ p₂ e₂;
    intro h,
    { refl, },
    { exfalso,
      simp at h, cases h with h h',
      rw [←path.eq_cast_iff_heq rfl h.symm, path.cast_cons] at h',
      exact (path.nil_ne_cons _ _) h', },
    { exfalso,
      simp at h, cases h with h h',
      rw [←path.cast_eq_iff_heq rfl h, path.cast_cons] at h',
      exact (path.cons_ne_nil _ _) h', },
    { simp only [prefunctor.path_star_apply, prefunctor.map_path_cons] at h, cases h with hφy h',
      rw [←path.cast_eq_iff_heq rfl hφy, path.cast_cons, path.cast_rfl_rfl] at h',
      have hφx := path.obj_eq_of_cons_eq_cons h',
      have hφp := path.heq_of_cons_eq_cons h',
      have hφe := heq.trans (hom.cast_heq rfl hφy _).symm (path.hom_heq_of_cons_eq_cons h'),
      have h_path_star : φ.path_star u ⟨x₁, p₁⟩ = φ.path_star u ⟨x₂, p₂⟩,
      { ext, exact hφx, exact hφp },
      specialize ih h_path_star, cases ih,
      have h_star : φ.star x₁ ⟨y₁, e₁⟩ = φ.star x₁ ⟨y₂, e₂⟩,
      { ext, exact hφy, exact hφe, },
      cases (hφ.1 x₁).1 h_star, refl, },  },
  { rintro ⟨v,p⟩,
    induction p with v' v'' p' ev ih,
    { simp only [prefunctor.path_star_apply, path_star_eq_iff, sigma.exists],
      exact ⟨u,path.nil,rfl,rfl⟩, },
    { obtain ⟨⟨u',q'⟩,h⟩ := ih,
      rw path_star_eq_iff at h,
      obtain ⟨h',h''⟩ := h,
      cases h', cases h'',
      obtain ⟨⟨u'',eu⟩,k⟩ := (hφ.left u').right ⟨_,ev⟩,
      rw star_eq_iff at k,
      obtain ⟨k',k''⟩ := k,
      cases k', cases k'',
      use ⟨_,q'.cons eu⟩,
      simp only [prefunctor.path_star_apply, prefunctor.map_path_cons, eq_self_iff_true,
                 heq_iff_eq, and_self], } }
end

section has_involutive_reverse

variables [has_involutive_reverse U] [has_involutive_reverse V] [prefunctor.preserves_reverse φ]

@[simps] def star_equiv_costar (u : U) :
  star u ≃ costar u :=
⟨λ e, ⟨e.1, reverse e.2⟩, λ e, ⟨e.1, reverse e.2⟩, λ e, by simp, λ e, by simp⟩

@[simp] lemma star_equiv_costar_apply {u v : U} (e : u ⟶ v) :
  star_equiv_costar u ⟨v, e⟩ = ⟨v, reverse e⟩ := rfl
@[simp] lemma star_equiv_costar_symm_apply {u v : U} (e : v ⟶ u) :
  (star_equiv_costar u).symm ⟨v, e⟩ = ⟨v, reverse e⟩ := rfl

lemma prefunctor.costar_conj_star
   (u : U) :
  (φ.costar u) = (star_equiv_costar (φ.obj u)) ∘ (φ.star u) ∘ (star_equiv_costar u).symm :=
begin
  ext e; cases e with v e; simp,
end

lemma prefunctor.bijective_costar_iff_bijective_star (u : U) :
  function.bijective (φ.costar u) ↔ function.bijective (φ.star u) :=
begin
  rw [prefunctor.costar_conj_star, function.bijective.of_comp_iff', function.bijective.of_comp_iff];
  exact equiv.bijective  _,
end

def prefunctor.is_covering_of_bijective_star (h : ∀ u, function.bijective (φ.star u)) :
  φ.is_covering := ⟨h, λ u, (φ.bijective_costar_iff_bijective_star u).2 (h u)⟩

def prefunctor.is_covering_of_bijective_costar (h : ∀ u, function.bijective (φ.costar u)) :
  φ.is_covering := ⟨λ u, (φ.bijective_costar_iff_bijective_star u).1 (h u), h⟩

end has_involutive_reverse

section cover_automorphisms

set_option old_structure_cmd true
structure iso (V W : Type*) [quiver V] [quiver W] :=
(to_prefunctor : V ⟶q W)
(inv_prefunctor : W ⟶q V)
(left_inv : to_prefunctor ≫q inv_prefunctor = 𝟙q V)
(right_inv : inv_prefunctor ≫q to_prefunctor = 𝟙q W)

structure cover_endo :=
(to_prefunctor : U ⟶q U)
(cover : to_prefunctor ≫q φ = φ)

structure cover_auto extends (iso U U), (cover_endo φ)

end cover_automorphisms
-/

end quiver
