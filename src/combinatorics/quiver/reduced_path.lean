import combinatorics.quiver.basic
import combinatorics.quiver.path
import data.sum.basic
import logic.relation
import tactic.linarith
import combinatorics.quiver.symmetric

universes v u

namespace quiver

open relation

variables {V : Type*} [quiver.{v+1} V] [has_involutive_reverse V]

def red.step {X Y : V} (p q : path X Y) :=
  ∃ (Z W : V) (pre : path X Z) (f : Z ⟶ W) (suf : path Z Y),
               p = (pre.comp ((path.nil.cons f).cons (reverse f))).comp suf ∧
               q = pre.comp suf

abbreviation red.step_refl {X Y : V} (p q : path X Y) : Prop := refl_gen red.step p q
abbreviation red  {X Y : V}  (p q : path X Y) : Prop := refl_trans_gen (red.step) p q
abbreviation red.symm  {X Y : V}  (p q : path X Y) : Prop := join (red) p q

lemma red.step_length_lt {X Y : V} (p q : path X Y) : red.step p q → q.length < p.length :=
begin
  rintro FS,
  obtain ⟨Z,W,pre,f,suf,rfl,rfl⟩ := FS,
  simp only [path.length_comp, path.comp_cons, path.comp_nil, path.length_cons],
  linarith only [],
end


def path.is_reduced {X Y : V} (p : path X Y) := ∀ q, ¬ red.step p q

-- can get a constructive version of this?
-- probably, with enough work
def path.exists_is_reduced {X Y : V} [∀ p : path X Y, decidable p.is_reduced] :
   Π (p : path X Y), ∃ (r : path X Y), (red p r ∧ r.is_reduced)
| p := if h : p.is_reduced then ⟨p, by {apply refl_trans_gen.refl}, h⟩ else by
  { dsimp [path.is_reduced] at h, push_neg at h,
    obtain ⟨q,qp⟩ := h,
    let : q.length < p.length := red.step_length_lt p q qp, -- hint for well-foundedness
    obtain ⟨r, rq, rred⟩ := path.exists_is_reduced q,
    refine ⟨r, _, rred⟩,
    exact refl_trans_gen.trans (refl_trans_gen.single qp) rq, }
using_well_founded
{ dec_tac := `[assumption],
  rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ (p : path X Y), p.length)⟩] }

lemma path.nil_is_reduced {X : V} : (path.nil : path X X).is_reduced :=
begin
  rintro p ⟨_,_,_,_,_,h',h''⟩,
  replace h' := congr_arg (path.length) h',
  simp only [path.length_nil, path.comp_cons, path.comp_nil, path.length_comp,
             path.length_cons] at h',
  linarith only [h'],
end

lemma path.to_path_is_reduced {X Y : V} (f : X ⟶ Y) : f.to_path.is_reduced :=
begin
  rintro p ⟨_,_,_,_,_,h',h''⟩,
  replace h' := congr_arg (path.length) h',
  simp only [hom.to_path, path.length_cons, path.length_nil, zero_add, path.comp_cons, path.comp_nil, path.length_comp] at h',
  linarith only [h'],
end

lemma path.is_not_reduced_iff {X Y : V} (p : path X Y) : ¬ p.is_reduced ↔
  ∃ (Z W : V) (pre : path X Z) (f : Z ⟶ W) (suf : path Z Y),
    p = (pre.comp ((path.nil.cons f).cons (reverse f))).comp suf :=
begin
  dsimp [path.is_reduced], push_neg,
  split,
  { rintro ⟨_,Z,W,pre,f,suf,rfl, rfl⟩, exact ⟨Z,W,pre,f,suf,rfl⟩, },
  { rintro ⟨Z,W,pre,f,suf,rfl, rfl⟩, exact ⟨pre.comp suf, Z,W,pre,f,suf,rfl, rfl⟩, },
end


lemma path.cons_cons_is_reduced {X Y Z W : V} (p : path X Y) (f : Y ⟶ Z) (g : Z ⟶ W) :
((p.cons f).cons g).is_reduced ↔ (p.cons f).is_reduced ∧ ¬ (∃ h : Y = W, h.rec_on f = reverse g) :=
begin
  classical,
  rw [←decidable.not_iff_not, not_and_distrib, path.is_not_reduced_iff, path.is_not_reduced_iff],
  split,
  { rintro ⟨z,w,pre,h,suf,hl⟩,
    cases suf,
    { tidy,
      right,
      subst_vars,
      rw reverse_reverse, },
    { tidy,
      simp only [*],
      left,
      refine ⟨_,_,pre,h,_,rfl⟩, },
     },
  { rintro (⟨z,w,pre,h,suf,hl⟩|hy),
    { simp only [path.comp_cons, path.comp_nil] at hl ⊢,
      refine ⟨_,_,pre,h,suf.cons g,_⟩,
      simp only [path.comp_cons, eq_self_iff_true, heq_iff_eq, and_self, hl], },
    { simp only [not_exists, not_forall, not_not] at hy,
      obtain ⟨rfl,a⟩ := hy,
      simp only at a,
      obtain rfl := a,
      refine ⟨_,_,p,reverse g,path.nil,_⟩,
      simp only [path.comp_cons, path.comp_nil, reverse_reverse, path.comp_nil,
                 eq_self_iff_true, heq_iff_eq, and_self], }, }
end


lemma path.is_reduced_of_cons_is_reduced {X Y Z : V} (p : path X Y) (e : Y ⟶ Z)
  (h : (p.cons e).is_reduced) : p.is_reduced :=
begin
  rintro q ⟨_,_,pre,f,suf,rfl,rfl⟩,
  exact h (pre.comp (suf.cons e)) ⟨_,_,pre,f,suf.cons e,rfl,rfl⟩,
end

lemma path.cons_comp_is_reduced {X Y Z W : V} (p : path X Y) (f : Y ⟶ Z) (q : path Z W) :
  ((p.cons f).comp q).is_reduced ↔ (p.cons f).is_reduced ∧ (f.to_path.comp q).is_reduced :=
begin
  induction q with _ _ q g hi,
  { simp only [path.comp_nil, iff_self_and],
    rintro, apply path.to_path_is_reduced, },
  { induction q with _ _ q h hi',
    { simp only [quiver.hom.to_path, path.cons_cons_is_reduced, path.comp_cons, path.comp_nil,
                 not_exists, and.congr_right_iff, iff_and_self],
      rintros, apply path.to_path_is_reduced, },
    { simp only [quiver.hom.to_path, path.cons_cons_is_reduced, path.comp_cons] at hi ⊢,
      simp only [hi],
      exact ⟨λ ⟨hl,hr⟩, ⟨hl.left,hl.right,hr⟩,λ ⟨hl,hr,hrr⟩, ⟨⟨hl,hr⟩,hrr⟩⟩, }, },
end

lemma path.reverse_is_reduced {X Y : V} {p : path X Y} (hp : p.is_reduced) : p.reverse.is_reduced :=
begin
  induction p with _ _ p f hi,
  { exact path.nil_is_reduced, },
  { induction p with _ _ p g hi',
    { apply path.to_path_is_reduced, },
    { simp at *, }, },
end

lemma path.comp_reverse_is_reduced {X Y Z W : V}
  (p : path X Y) (e : Y ⟶ W) (q : path X Z) (f : Z ⟶ W)
  (hp : (p.cons e).is_reduced) (hq : (q.cons f).is_reduced) (hYZ : Y ≠ Z) :
  ((p.cons e).comp (q.cons f).reverse).is_reduced := sorry

lemma path.comp_reverse_is_reduced' {X Y W : V}
  (p : path X Y) (e : Y ⟶ W) (q : path X Y) (f : Y ⟶ W)
  (hp : (p.cons e).is_reduced) (hq : (q.cons f).is_reduced) (hef : e ≠ f) :
  ((p.cons e).comp (q.cons f).reverse).is_reduced := sorry


@[reducible]
def path.is_cyclically_reduced {X : V} (p : path X X) :=
  ∀ {Y : V} (q : path X Y) (r : path Y X), q.comp r = p → (r.comp q).is_reduced

lemma path.is_reduced_of_is_cyclically_reduced {X : V} (p : path X X)
  (hp : p.is_cyclically_reduced) : p.is_reduced :=
by { simpa using (hp p path.nil), }

variable (V)

@[reducible]
def is_forest := ∀ (X Y : V) (p q : path X Y), p.is_reduced → q.is_reduced → p = q
@[reducible]
def no_reduced_circuit := ∀ (X : V) (p : path X X), p.is_reduced → p = path.nil
@[reducible]
def no_cyclically_reduced_circuit := ∀ (X : V) (p : path X X),
  p.is_cyclically_reduced → p = path.nil

lemma no_reduced_circuit_of_no_cyclically_reduced_circuit :
  no_cyclically_reduced_circuit V → no_reduced_circuit V := sorry

lemma no_reduced_circuit_iff_no_cyclically_reduced_circuit :
  no_reduced_circuit V ↔ no_cyclically_reduced_circuit V :=
⟨λ h X p hp, h X p (p.is_reduced_of_is_cyclically_reduced hp),
 no_reduced_circuit_of_no_cyclically_reduced_circuit V⟩

lemma is_forest_of_no_reduced_circuit' (h : no_reduced_circuit V) (x : V) :
  ∀ (y : V) (p q : path x y), p.is_reduced → q.is_reduced → p = q
| _ (path.nil) (path.nil) hp hq := rfl
| _ (path.cons p e) (path.nil) hp hq := h _ _ hp
| _ (path.nil) (path.cons q f) hp hq := (h _ _ hq).symm
| _ pp@(@path.cons _ _ _ z y p e) qq@(@path.cons _ _ _ w _  q f) hp hq := by
  { have pr : p.is_reduced := p.is_reduced_of_cons_is_reduced e hp,
    have qr : q.is_reduced := q.is_reduced_of_cons_is_reduced f hq,
    by_cases zw : z = w,
    { induction zw,
      by_cases ef : e = f,
      { induction ef,
        cases is_forest_of_no_reduced_circuit' z p q pr qr,
        refl, },
      { simpa using
          (congr_arg path.length (h _ _ (path.comp_reverse_is_reduced' p e q f hp hq ef))),
      } },
    { simpa using
        (congr_arg path.length (h _ _ (path.comp_reverse_is_reduced p e q f hp hq zw))), }, }

lemma is_forest_of_no_reduced_circuit (h : no_reduced_circuit V) : is_forest V :=
is_forest_of_no_reduced_circuit' V h


lemma is_forest_iff :
  is_forest V ↔ ∀ (X : V) (p : path X X), p.is_reduced → p = path.nil :=
begin
  split,
  { rintro h X p hp, exact h X X p (path.nil) hp nil_is_reduced, },
  { sorry  }
end


lemma is_connected_iff :
  is_connected V ↔ ∀ (X Y : V), ∃ (p : path X Y), p.is_reduced :=
begin
  classical,
  split,
  { rintro h X Y,
    obtain ⟨r,rred⟩ := path.exists_is_reduced (h X Y).some,
    exact ⟨r,rred.right⟩, },
  { rintro h X Y,
    exact ⟨(h X Y).some⟩, },
end

end quiver
