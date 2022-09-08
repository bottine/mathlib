import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.prod
import combinatorics.simple_graph.metric

import topology.metric_space.basic
import data.setoid.partition

open function
open finset
open set
open classical
open simple_graph.walk
open relation
universes u v w



noncomputable theory
local attribute [instance] prop_decidable
-- to make every proposition decidable

variables  {V : Type u}
           (G : simple_graph V)
           --[preconnected G]
           --[locally_finite G]

namespace simple_graph


lemma walk.split_along_set {V : Type u} {G : simple_graph V} :
∀ {u v : V} (p : G.walk u v) (S : set V) (uS : u ∈ S) (vS : v ∉ S),
  ∃ (x y : V) (w : G.walk u x) (a : G.adj x y) (w' : G.walk y v), p = w.append (cons a w') ∧  (w.support.to_finset : set V) ⊆ S ∧ y ∉ S
| _ _ nil p uS vnS := (vnS uS).elim
| _ _ (cons' u x v a w) S uS vnS := by
{ by_cases h : S x,
  { obtain ⟨x',y,w',a',w'',weq,wS,ynS⟩ := walk.split_along_set w S h vnS,
    use [x',y,cons a w',a',w''],
    split,
    { simp only [cons_append,weq], },
    { simp only [support_cons, list.to_finset_cons, coe_insert,set.insert_subset],
      exact ⟨⟨uS,wS⟩,ynS⟩,}
  },
  { use [u,x,nil,a,w],
    simp only [nil_append, eq_self_iff_true, support_nil, list.to_finset_cons,
      list.to_finset_nil, insert_emptyc_eq, coe_singleton, set.singleton_subset_iff,true_and],
    exact ⟨uS,h⟩, }
}


lemma walk.mem_support_to_exists_append  {V : Type u} {G : simple_graph V} {u v w : V} {p : G.walk u v} (h : w ∈ p.support) :
  ∃ (q : G.walk u w) (r : G.walk w v), p = q.append r :=
match u, v, w, p, h with
| _, _, _, (nil' x), e            := by { simp at e, induction e, use nil, use nil, simp, }
| _, _, _, (cons' x y z a p'), e := by {
  simp at e,
  induction e,
  { rcases e with rfl,
    use nil, simp,
  },
  { rcases _match _ _ _ p' e with ⟨r',q',e'⟩,
    use cons a r', use q',simp only [e', cons_append],},
}
end

lemma walk.mem_support_iff_exists_append  {V : Type u} {G : simple_graph V} {u v w : V} {p : G.walk u v} :
  w ∈ p.support ↔ ∃ (q : G.walk u w) (r : G.walk w v), p = q.append r :=
begin
  split,
  { exact walk.mem_support_to_exists_append },
  { rintros ⟨q,r,rfl⟩,simp only [mem_support_append_iff, end_mem_support, start_mem_support, or_self],},
end

lemma walk.support_append_subset_left {V : Type u} {G : simple_graph V} {u v w : V} (p : G.walk u v) (q : G.walk v w) :
  p.support ⊆ (p.append q).support := by simp only [walk.support_append,list.subset_append_left]

lemma walk.support_append_subset_right {V : Type u} {G : simple_graph V} {u v w : V} (p : G.walk u v) (q : G.walk v w) :
  q.support ⊆ (p.append q).support := by {
    rw walk.support_append,
    induction q,
    {simp only [support_nil, list.tail_cons, list.append_nil, list.cons_subset, end_mem_support, list.nil_subset, and_self],},
    {simp only [support_cons, list.tail_cons, list.cons_subset, list.mem_append, end_mem_support, true_or, list.subset_append_right,and_self],},
  }


lemma walk.pred_adj_non_pred {V : Type u} {G : simple_graph V} :
∀ (u v : V) (p : G.walk u v) (S : set V) (upred : u ∈ S) (vnpred : v ∉ S),
  ∃ (x y : V), G.adj x y ∧ x ∈ S ∧ y ∉ S
| _ _ nil p up vnp := (vnp up).elim
| _ _ (cons' x y z a q) p up vnp := if h : p y then walk.pred_adj_non_pred y z q p h vnp else ⟨x,y,a,up,h⟩


lemma simple_graph.walk.support_box_prod_left {α : Type*} {β : Type*}
  {G : simple_graph α} (H : simple_graph β) {a₁ a₂ : α} (b : β) (w : G.walk a₁ a₂) :
  (walk.box_prod_left H b w).support = w.support.map (λ x, ⟨x,b⟩) := sorry

lemma simple_graph.walk.support_box_prod_right {α : Type*} {β : Type*}
  (G : simple_graph α) {H : simple_graph β} {b₁ b₂ : β} (a : α)
  (w : H.walk b₁ b₂) : (walk.box_prod_right G a w).support = w.support.map (λ x, ⟨a,x⟩) := sorry



def is_prefix {V : Type*} {G : simple_graph V} : Π {u v w : V} (r : G.walk u w) (p : G.walk u v), Prop
| _ _ _ nil nil := true
| _ _ _ nil (cons _ _) := true
| u v w (cons _ _) nil := false
| u _ _ (cons' x yr v a r') (cons' xp yp w b p') := ∃ (e : yr = yp), @is_prefix yp w v (eq.rec r' e) p'

infix ` ≤w ` : 50 := is_prefix

lemma is_prefix_to_exists_suffix  {V : Type*} {G : simple_graph V} :
  Π {u v w : V} (r : G.walk u w) (p : G.walk u v),  r ≤w p → ∃ q : G.walk w v, r.append q = p
| _ _ _ nil nil := by {rintro _, use nil, simp,}
| _ _ _ nil (cons a p) := by { rintro _, use cons a p, simp,}
| u v w (cons _ _) nil := by {rintro f,unfold is_prefix at f,exfalso,exact f}
| u _ _ (cons' x yr v a r') (cons' xp yp w b p') := by { rintro le, unfold is_prefix at le, rcases le with ⟨rfl,le'⟩, simp at le',rcases is_prefix_to_exists_suffix r' p' le' with ⟨q,rfl⟩,use q,simp,}

lemma is_prefix_of_exists_suffix  {V : Type*} {G : simple_graph V} :
  Π {u v w : V} (r : G.walk u w) (p : G.walk u v),  (∃ q : G.walk w v, r.append q = p) → r ≤w p
| _ _ _ nil nil := by {simp,}
| _ _ _ nil (cons a p) := by {simp,}
| u v w (cons _ _) nil := by {simp,}
| u _ _ (cons' x yr v a r') (cons' xp yp w b p') := by { rintros ⟨q,qeq⟩,
  induction qeq,
  rcases is_prefix_of_exists_suffix r' (r'.append q) ⟨q,rfl⟩ with le,
  exact ⟨rfl,le⟩,
  }

lemma is_prefix.nil  {V : Type*} {G : simple_graph V} :
  Π {u w : V} (r : G.walk u w), nil ≤w r
| _ _ nil := trivial
| _ _ (cons _ _) := trivial


lemma is_prefix.refl  {V : Type*} {G : simple_graph V} :
  Π {u w : V} (r : G.walk u w), r ≤w r
| _ _ nil := trivial
| _ _ (cons' x y z a p) := ⟨rfl,is_prefix.refl p⟩

lemma is_prefix.rfl  {V : Type*} {G : simple_graph V} :
  Π {u w : V} {r : G.walk u w}, r ≤w r := λ u w r, is_prefix.refl r

lemma is_prefix.trans  {V : Type*} {G : simple_graph V} :
  Π {u v w z : V} {r : G.walk u v} {p : G.walk u w} {q : G.walk u z}, r ≤w p → p ≤w q → r ≤w q
| _ _ _ _ nil nil nil e f := trivial
| _ _ _ _ nil nil (cons _ _) e f := trivial
| _ _ _ _ nil (cons _ _) nil e f := f.elim
| _ _ _ _ nil (cons _ _) (cons _ _) e f := trivial
| _ _ _ _ (cons _ _) nil nil e f := e.elim
| _ _ _ _ (cons _ _) nil (cons _ _) e f := e.elim
| _ _ _ _ (cons _ _) (cons _ _) nil e f := f.elim
| _ _ _ _ (cons' xr yr zr ar r) (cons' xp yp zp ap p) (cons' xq yq zq aq q) e f := by {
   rcases e with ⟨rfl,e'⟩,
   rcases f with ⟨rfl,f'⟩,
   refine ⟨rfl,_⟩,
   --squeeze_simp,
   --simp at e',
   --simp at f',
   exact is_prefix.trans e' f',}

def is_prefix.eq_nil_of_nil  {V : Type*} {G : simple_graph V} :
  Π {u v : V} {r : G.walk u v} (pfx : r ≤w nil), ∃ (e : v = u), @eq.rec V v (λ x, G.walk u x) r u e = nil' u
| _ _ (nil' u) pfx := ⟨rfl,rfl⟩
| _ _ (cons' u v w a r) pfx := pfx.elim

noncomputable def longest_prefix_all {V : Type*} {G : simple_graph V} :
Π {u v: V} (p : G.walk u v) (pred : ∀ (z : V) (q : G.walk u z), q ≤w p → Prop) ,
psum
  { R : Σ (z : V), G.walk u z | ∃ (pfxR : R.2 ≤w p) (predR : pred R.1 R.2 pfxR),
                                ∀ z (q : G.walk u z) (pfxq : q ≤w p), pred z q pfxq → q ≤w R.2 }
  (∀ (z : V) (q : G.walk u z) (pfx : q ≤w p), ¬ pred z q pfx)
| _ _ (nil' x) pred := by {
  simp only [exists_prop, exists_and_distrib_right, coe_set_of] at *,
  by_cases h : pred x (nil' x) (is_prefix.rfl),
  { left,
    use [x,is_prefix.rfl,h],
    rintros z q pfx hh,
    exact pfx,},
  { right,
    rintros z q pfx,
    rcases is_prefix.eq_nil_of_nil pfx with ⟨rfl,eq'⟩,
    induction eq',
    exact h,}
  }
| _ _ (cons' x y z a p) pred := by {
  let pred' :  ∀ (w : V) (q : G.walk y w), q ≤w p → Prop
            := λ w q pfx, pred w (cons' x y w a q) (by { refine ⟨rfl,_⟩, exact pfx,}), -- why need to refine
  rcases longest_prefix_all p pred' with ⟨⟨t,r⟩,good⟩|bad,
  { left,
    use ⟨t,cons a r⟩,
    rcases good with ⟨pfxr,predr,maxr⟩, -- Can only split here since otherwise we're not in a Prop yet
    use [⟨rfl,pfxr⟩,predr],
    rintros z q pfxq predq ,
    cases q,
    { simp only, },
    { rcases pfxq with ⟨rfl,pfxq'⟩,
      exact ⟨rfl,maxr _ _ pfxq' predq⟩,},
  },
  { by_cases h : pred x nil (is_prefix.nil (cons a p)),
    { left,
      use [⟨x,nil⟩,is_prefix.nil (cons a p),h],
      rintros z q pfxq predq,
      cases q,
      { simp only, },
      { rcases pfxq with ⟨rfl,pfxq'⟩, exact (bad z q_p pfxq' predq).elim,},},
    { right, rintro z q pfxq,
      cases q,
      { exact h, },
      { rcases pfxq with ⟨rfl,pfxq'⟩, exact bad _ q_p pfxq',},},
  },
}


def thicken  {V : Type*} (G : simple_graph V) (K : set V) :
  set V := K ∪ {v : V | ∃ k : K, G.adj k v}

lemma thicken.finite {V : Type*} (G : simple_graph V) [Glf : G.locally_finite]  (K : finset V) :
  (thicken G K).finite :=
begin
  have : G.thicken K = K ∪ (set.Union (λ x : K, G.neighbor_set x)), by {
    simp only [thicken,neighbor_set], apply congr_arg _,
    ext, rw mem_Union, simp only [mem_set_of_eq], refl,},
  rw this,
  apply set.finite_union.mpr, split, exact set.to_finite K,
  haveI : finite (↥K), by {apply finite_coe_iff.mpr, exact to_finite K,},
  apply set.finite_Union, rintro ⟨x,xk⟩,
  apply set.finite_def.mpr, constructor, exact Glf x,
end

lemma thicken.of_all_adj {V : Type*} (G : simple_graph V) (K : set V) (Kadj : ∀ k ∈ K, ∃ k' ∈ K, G.adj k k') : thicken G K = {v : V | ∃ k ∈ K, G.adj v k} :=
begin
  unfold thicken,
  ext,
  split,
  {
    intro h,
    cases h,
    { exact Kadj _ h,},
    -- tidy
    { cases h, cases h_w, dsimp at *, simp at *, fsplit, work_on_goal 2 { fsplit, work_on_goal 1 { assumption }, solve_by_elim }},
  },
  { intro h, right,
    -- tidy
    {cases h, cases h_h, dsimp at *, simp at *, fsplit, work_on_goal 2 { fsplit, work_on_goal 1 { assumption }, solve_by_elim }}}
end

#check nonempty.elim

lemma thicken.of_connected {V : Type*} (G : simple_graph V) (K : set V) (Kconn : (G.induce K).connected) : thicken G K = {v : V | ∃ k ∈ K, G.adj v k} :=
begin
  refine thicken.of_all_adj G K _,
  intros k hkK,
  cases Kconn,
  apply Kconn_nonempty.elim,
  rintro k',
  let p := (Kconn_preconnected ⟨k, hkK⟩ k').some,
  sorry,
end

@[reducible]
def neighborhood  {V : Type*} (G : simple_graph V) [locally_finite G] [preconnected G]
  (S : set V) (n : ℕ) := {v : V | ∃ s ∈ S, G.dist s v ≤ n}

lemma neighborhood.zero  {V : Type*} {G : simple_graph V} [lc : locally_finite G] [pc : preconnected G]  (S : set V) :
  @neighborhood V G lc pc S 0 = S := sorry

lemma neighborhood.succ {V : Type*} (G : simple_graph V) [lc : locally_finite G] [pc : preconnected G]  (S : set V) (n : ℕ) :
  @neighborhood V G lc pc S (n+1) = ⋃ v ∈ @neighborhood V G lc pc S n, G.neighbor_set v := sorry


def neighborhood_finite {V : Type*} (G : simple_graph V) [lc : locally_finite G] [pc : preconnected G]
  (S: set V) (Sfin : S.finite) : Π (n : ℕ), (@neighborhood V G lc pc S n).finite
| 0 := by {convert Sfin, apply neighborhood.zero,}
| (n+1) := by
{ rw neighborhood.succ,
  apply set.finite.bUnion,
  exact @neighborhood_finite n,
  rintro i iS,
  exact (neighbor_set G i).to_finite,
}



--mathlib
@[reducible, simp] def connected_component.supp {G : simple_graph V} (C : G.connected_component) :=
  {v : V | connected_component_mk G v = C}

--mathlib
@[ext] lemma connected_component.eq_of_eq_supp (C D : G.connected_component) : C = D ↔ C.supp = D.supp :=
begin
  split,
  { intro h, subst h, },
  { refine connected_component.ind₂ _ C D,
    intros v w h,
    simp_rw [set.ext_iff] at h,
    apply (h v).mp, dsimp [connected_component.supp],
    refl,}
end

--mathlib
instance : set_like G.connected_component V := {
  coe := connected_component.supp,
  coe_injective' := by {intros C D, apply (connected_component.eq_of_eq_supp _ _ _).mpr, } }

-- Some variation of this should surely be included in mathlib ?!
--mathlib
lemma connected_component.connected (C : G.connected_component) :
(G.induce C.supp).connected :=
begin
  revert C,
  refine connected_component.ind _,
  rintro v,
  let comp := (G.connected_component_mk v).supp,
  rw connected_iff,
  fsplit,
  { suffices : ∀ u : comp, (G.induce comp).reachable u ⟨v, by {dsimp [comp], refl,}⟩,
    { exact λ u w, (this u).trans (this w).symm, },

    rintro ⟨u,uv⟩,
    simp only [mem_set_of_eq, connected_component.eq] at uv,
    obtain ⟨uv'⟩ := uv,
    induction uv' with a b c d e f g,
    { refl, },
    { --have : c ∈ C, by {simp at uv ⊢, constructor, exact f,},
      simp only [mem_set_of_eq, connected_component.eq] at *,
      constructor,
      apply walk.cons, rotate,
      exact (g ⟨f⟩).some,
      simp only [comap_adj, embedding.coe_subtype, subtype.coe_mk],
      exact e,}},
  { simp [connected_component.supp], use v, }
end

--mathlib
lemma connected_component.of_preconnected (Gpc : G.preconnected) (C : G.connected_component)
: (C : set V) = univ :=
begin
  sorry
end

-- mathlib
def connected_component.equiv_of_iso {V V' : Type*} {G : simple_graph V} {G' : simple_graph V'}
  (φ : G ≃g G') : G.connected_component ≃ G'.connected_component :=
begin
  fsplit,
  { fapply connected_component.lift,
    { rintro v, exact connected_component_mk G' (φ v),},
    { rintro v w p pp, simp only [connected_component.eq], constructor, exact p.map φ.to_hom,}},

  { fapply connected_component.lift,
    { rintro v, exact connected_component_mk G (φ.symm v),},
    { rintro v w p pp, simp only [connected_component.eq], constructor, exact p.map φ.symm.to_hom,}},
  { dsimp only [function.right_inverse,function.left_inverse],
    apply connected_component.ind,
    simp only [connected_component.eq, connected_component.lift_mk, rel_iso.symm_apply_apply],
    rintro v, refl},
  { dsimp only [function.right_inverse,function.left_inverse],
    apply connected_component.ind,
    simp only [connected_component.eq, connected_component.lift_mk, rel_iso.symm_apply_apply],
    rintro v, simp only [rel_iso.apply_symm_apply], }
end


--mathlib (it seems mathlib only has this for subgraph with subset of vertices ?)
def is_subgraph.hom {G G' : simple_graph V} (h : G ≤ G') : G →g G' := ⟨id, h⟩


lemma preconnected_of_all_adj {α : Type*} {k : finset V} (kconn : (G.induce ↑k).connected)
  {S : α → set V} {hS_fin : set.finite (set.Union S)} (hS_conn : ∀ {A : α},
  (G.induce (S A)).connected) : (∀ {A : α}, (∃ (ck : V × V), ck.1 ∈ S A ∧ ck.2 ∈ k ∧ G.adj ck.1 ck.2) ∨ (S A ⊆ ↑k)) →
    (G.induce ↑(k ∪ hS_fin.to_finset)).connected :=
begin
  intro h,
  rw connected_iff,
  split, {
    rintros vv ww,
    have hv := vv.prop, have hw := ww.prop,
    simp at hv hw,
    cases hv, cases hw,
    {
      sorry,
    }, {
      sorry,
    }, cases hw, {
      sorry,
    }, {
      sorry
    },
  },  {
    apply set.nonempty_coe_sort.mpr,
    apply set.nonempty.mono, rotate,
    rw [← set.nonempty_coe_sort],
    exact ((connected_iff _).mp kconn).2,
    simp, }
end

--mathlib
lemma iso.induce_restrict {V V' : Type*} {G : simple_graph V} {G' : simple_graph V'} (φ : G ≃g G')
  (s : set V) : (G.induce s) ≃g (G'.induce (φ '' s)) := sorry

--mathlib
lemma iso.connected {V V' : Type*} {G : simple_graph V} {G' : simple_graph V'} (φ : G ≃g G') :
  G.connected ↔ G'.connected := sorry


end simple_graph



namespace list

-- And this for lists:
@[simp]
lemma to_finset_tail {α : Type u} [decidable_eq α] (l : list α) : l.tail.to_finset ⊆ l.to_finset :=
match l with
| list.nil := by {simp only [list.tail_nil, list.to_finset_nil, finset.empty_subset],}
| list.cons h l := by {simp only [list.tail_cons, list.to_finset_cons], exact finset.subset_insert _ _}
end

lemma to_finset_subset_to_finset {α : Type u} [decidable_eq α] (l₁ l₂ : list α) (h : l₁ ⊆ l₂) : l₁.to_finset ⊆ l₂.to_finset :=
begin
  revert l₂,
  induction l₁,
  { intros l₂ h, simp only [list.to_finset_nil, finset.empty_subset], },
  { intros l₂ h,
    simp at h, cases h,
    simp only [list.to_finset_cons, finset.insert_subset],
    split,
    {
      revert h_left, generalizes [l₁_hd = a, l₂ = l],
      intro h, cases l,
      {simp at h, contradiction,},
      {simp at h ⊢, assumption, }
    },
    {apply l₁_ih, assumption, } }
end

lemma map_to_finset {α β : Type*}  [decidable_eq α]  [decidable_eq β] (f : α → β) (l : list α) :
  (l.map f).to_finset = finset.image f l.to_finset :=
list.rec_on l (by {simp}) (λ h t hyp, by {simp,rw hyp,})

end list


namespace simple_graph


lemma transitive_to_good_automs [locally_finite G] [G.preconnected]
  (trans : ∀ u v : V, ∃ φ : G ≃g G, φ u = v)
  (Vinf : (@set.univ V).infinite) :
   ∀ K :finset V, ∃ φ : G ≃g G, disjoint K (finset.image φ K) :=
begin
  sorry
end

-- This should be made compatible with the `simple_graph` API but for now we leave it aside
def subconnected (X : set V) := ∀ x y ∈ X, ∃ w : G.walk x y, ↑w.support.to_finset ⊆ X

lemma subconnected.of_adj_pair (x y : V) (e : G.adj x y) : subconnected G {x,y} :=
begin
  rintros a ain b bin,
  rcases ain with ⟨x,rfl⟩|⟨y,rfl⟩,
  { rcases bin with ⟨x,rfl⟩|⟨y,rfl⟩,
    { use walk.nil,simp,},
    { use walk.cons e (walk.nil), simp,},
  },
  { rcases bin with ⟨x,rfl⟩|⟨y,rfl⟩,
    { use walk.cons e.symm (walk.nil), rw [←list.to_finset_reverse,←walk.support_reverse],simp,},
    { use walk.nil,simp,},
  }
end

lemma subconnected.of_intersecting_subconnected {X Y : set V}
  (hX : subconnected G X )
  (hY : subconnected G Y )
  (hXY : ¬ disjoint X Y) : subconnected G (X∪Y) :=
begin
  rcases set.not_disjoint_iff.mp hXY with ⟨p,pX,pY⟩,
  rintros a aZ b bZ,
  rcases aZ with aX|aY,
  { rcases bZ with bX|bY,
    { rcases hX a aX b bX with ⟨w,wX⟩,
      exact ⟨w,wX.trans (set.subset_union_left X Y)⟩,},
    { rcases hX a aX p pX with ⟨w,wX⟩,
      rcases hY p pY b bY with ⟨u,uY⟩,
      use w.append u,
      rw [walk.support_append, list.to_finset_append,finset.coe_union],
      apply set.union_subset_union wX (set.subset.trans _ uY),
      apply list.to_finset_tail,
    },
  },
  { rcases bZ with bX|bY,
    { rcases hY a aY p pY with ⟨u,uY⟩,
      rcases hX p pX b bX with ⟨w,wX⟩,
      use u.append w,
      rw [walk.support_append, list.to_finset_append,finset.coe_union,set.union_comm],
      apply set.union_subset_union (set.subset.trans _ wX) uY,
      apply list.to_finset_tail,
    },
    { rcases hY a aY b bY with ⟨w,wY⟩,
      exact ⟨w,wY.trans (set.subset_union_right X Y)⟩,},
  },
end

lemma subconnected.of_adj_subconnected {X Y : set V}
  (hX : subconnected G X )
  (hY : subconnected G Y )
  (XYadj : ∃ (x ∈ X) (y ∈ Y), G.adj x y) : subconnected G (X∪Y) :=
begin
  rcases XYadj with ⟨x,xX,y,yY,e⟩,
  have : X∪Y = ({x, y} ∪ X) ∪ Y, by {ext, simp, tauto {closer := tactic.tidy.core >> tactic.skip},},
  rw this,
  apply subconnected.of_intersecting_subconnected,
  { apply subconnected.of_intersecting_subconnected,
    { exact subconnected.of_adj_pair G x y e, },
    { exact hX, },
    { exact set.not_disjoint_iff.mpr ⟨x,by simp,xX⟩},
  },
  { exact hY,},
  { exact set.not_disjoint_iff.mpr ⟨y,by simp,yY⟩}

end

lemma subconnected.image {U : Type*} (H : simple_graph U) (φ : G →g H)
  {X : finset V} (hX : subconnected G X) : (subconnected H (finset.image φ X)) :=
begin
    rintros φx xφ φy yφ,
    simp at xφ,
    simp at yφ,
    rcases xφ with ⟨x,⟨xK,rfl⟩⟩,
    rcases yφ with ⟨y,⟨yK,rfl⟩⟩,
    rcases hX x xK y yK with ⟨w,wgood⟩,
    rw finset.coe_subset at wgood,
    let φw := w.map φ,
    use φw,
    rw [walk.support_map,list.map_to_finset,finset.coe_subset],
    apply finset.image_subset_image wgood,
end

lemma subconnected.of_walk {x y : V} (w : G.walk x y) : subconnected G w.support.to_finset :=
begin
  rintros a ah b bh,
  simp at ah,
  simp at bh,
  rcases walk.mem_support_iff_exists_append.mp ah with ⟨wa,wa',eqa⟩,
  rcases walk.mem_support_iff_exists_append.mp bh with ⟨wb,wb',eqb⟩,
  use wa.reverse.append wb,
  simp,
  rw walk.support_append,
  rw list.to_finset_append,
  rw walk.support_reverse,
  rw list.to_finset_reverse,
  apply finset.union_subset,
  { rw eqa, apply list.to_finset_subset_to_finset, apply walk.support_append_subset_left,},
  { rw eqb,
    apply (list.to_finset_tail wb.support).trans _,
    apply list.to_finset_subset_to_finset,
    exact walk.support_append_subset_left wb wb',},
end

lemma subconnected.of_common_mem_sUnion (v : V) {F : set (set V)}
  (mem : ∀ S ∈ F, v ∈ S) (subconn : ∀ S ∈ F, subconnected G S) : subconnected G (⋃₀ F) :=
begin
  rintros x xh y yh,
  rcases xh with ⟨S,SF,xS⟩,
  rcases yh with ⟨T,TF,yT⟩,
  rcases subconnected.of_intersecting_subconnected G
         (subconn S SF)
         (subconn T TF)
         (set.not_disjoint_iff.mpr ⟨v,⟨mem S SF,mem T TF⟩⟩)
         x (by {simp *,})
         y (by {simp *,})
  with ⟨w,wgood⟩,
  use w,
  have : S ∪ T ⊆ ⋃₀ F, by {simp,exact ⟨subset_sUnion_of_mem SF,subset_sUnion_of_mem TF⟩},
  exact wgood.trans this,
end

end simple_graph


lemma  equiv.of_bijective_trans {α β γ : Type*} {f : α → β} {g : β → γ}
  (hf : function.bijective f) (hg : function.bijective g) :
(equiv.of_bijective f hf).trans (equiv.of_bijective g hg) = equiv.of_bijective (g ∘ f) (function.bijective.comp hg hf) :=
begin
  ext, simp,
end

lemma  equiv.of_bijective_inj {α β γ : Type*} {f : α → β}
  (h₁ h₂ : function.bijective f) :
(equiv.of_bijective f h₁) = (equiv.of_bijective f h₂) :=
begin
  ext, simp,
end


namespace finset

def bInter {α : Type*} (S : set (finset α)) (Snempty : S.nonempty) : finset α :=
{x ∈ Snempty.some | ∀ s ∈ S, x ∈ s}

lemma mem_bInter_iff {α : Type*} (S : set (finset α)) (Snempty : S.nonempty) (x : α) :
x ∈ (bInter S Snempty) ↔ (∀ s ∈ S, x ∈ s) :=
begin
  split,
  {rintro xI s sS, unfold bInter at xI, simp at xI, exact xI.2 s sS,},
  {rintro good, unfold bInter, simp only [sep_def, mem_filter], use good Snempty.some Snempty.some_spec, exact good,}
end





lemma bInter_of_directed_nonempty {α : Type*} (S : set (finset α)) (Snempty : S.nonempty)
  (allsnempty : ∀ s ∈ S, finset.nonempty s) (dir : directed_on (⊇) S) : finset.nonempty (bInter S Snempty) :=
begin
  let s₀ := function.argmin_on (finset.card) (nat.lt_wf) S Snempty,
  let hs₀ := argmin_on_mem (finset.card) (nat.lt_wf) S Snempty,
  suffices : s₀ = (bInter S Snempty), {
    rw ←this,
    exact allsnempty s₀ hs₀,},
  apply finset.ext,
  rintro x,
  split,
  { rintro xs₀,
    apply (mem_bInter_iff S Snempty x).mpr,
    rintro s hs,
    rcases dir s₀ hs₀ s hs with ⟨t,ht,ts₀,ts⟩,
    suffices : t = s₀,{
      rw this at ts,
      exact ts xs₀,},
    have : finset.card s₀ ≤ finset.card t, from function.argmin_on_le (finset.card) (nat.lt_wf) S ht,
    exact finset.eq_of_subset_of_card_le ts₀ this,
  },
  { rintro xI, exact (mem_bInter_iff S Snempty x).mp xI s₀ hs₀, },
end

end finset
