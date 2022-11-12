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

lemma nil_is_reduced {X : V} : (path.nil : path X X).is_reduced :=
begin
  rintro p h,
  obtain ⟨_,_,_,_,_,h',h''⟩ := h,
  replace h' := congr_arg (path.length) h',
  simp only [path.length_nil, path.comp_cons, path.comp_nil, path.length_comp,
             path.length_cons] at h',
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

lemma path.is_reduced_of_cons_is_reduced {X Y Z : V} (p : path X Y) (e : Y ⟶ Z)
  (h : (p.cons e).is_reduced) : p.is_reduced :=
begin
  rintro q ⟨_,_,pre,f,suf,rfl,rfl⟩,
  exact h (pre.comp (suf.cons e)) ⟨_,_,pre,f,suf.cons e,rfl,rfl⟩,
end

lemma path.comp_reverse_is_reduced {X Y Z W : V}
  (p : path X Y) (e : Y ⟶ W) (q : path X Z) (f : Z ⟶ W)
  (hp : (p.cons e).is_reduced) (hq : (q.cons f).is_reduced) (hYZ : Y ≠ Z) :
  ((p.cons e).comp (q.cons f).reverse).is_reduced := sorry

lemma path.comp_reverse_is_reduced' {X Y W : V}
  (p : path X Y) (e : Y ⟶ W) (q : path X Y) (f : Y ⟶ W)
  (hp : (p.cons e).is_reduced) (hq : (q.cons f).is_reduced) (hef : e ≠ f) :
  ((p.cons e).comp (q.cons f).reverse).is_reduced := sorry

abbreviation path.shift_cons {X Y : V} (p : path X Y) (e : Y ⟶ X) : path Y Y := e.to_path.comp p

def path.cons_is_cyclically_reduced' {X Y : V} (p : path X Y) (e : Y ⟶ X) :=
  (p.cons e).is_reduced ∧ (p.shift_cons e).is_reduced

@[simp] def path.is_cyclically_reduced' : Π {X Y : V} (p : path X X) (XY : X = Y), Prop
| _ _ path.nil _ := true
| _ _ (path.cons p e) _ := p.cons_is_cyclically_reduced' e

@[reducible]
def path.is_cyclically_reduced {X : V} (p : path X X) := p.is_cyclically_reduced' rfl

lemma path.is_reduced_of_is_cyclically_reduced {X : V} (p : path X X)
  (hp : p.is_cyclically_reduced) : p.is_reduced :=
begin
  dsimp [path.is_cyclically_reduced] at hp, cases p,
  { exact nil_is_reduced, },
  { exact hp.left, },
end

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

def tuple_len : (Σ' (X Y Z : V) (p : path X Y) (q : path X Z) (h : p.is_reduced), q.is_reduced) → ℕ :=
λ ⟨X,Y,Z,p,q,pr,qr⟩, p.length

/- This well foundedness trick seems like magic: `tuple_len` here is not actually the same function
   as the one used to compute well foundedness …
-/
lemma is_forest_of_no_reduced_circuit (h : no_reduced_circuit V) : is_forest V
| _ _ (path.nil) (path.nil) hp hq := rfl
| _ _ (path.cons p e) (path.nil) hp hq := h _ _ hp
| _ _ (path.nil) (path.cons q f) hp hq := (h _ _ hq).symm
| _ _ pp@(@path.cons _ _ x z y p e) qq@(@path.cons _ _ _ w _  q f) hp hq := by
  { have pr : p.is_reduced := p.is_reduced_of_cons_is_reduced e hp,
    have qr : q.is_reduced := q.is_reduced_of_cons_is_reduced f hq,
    --have : tuple_len V ⟨_,_,_,p,q,pr,qr⟩ < tuple_len V ⟨_,_,_,p.cons e,q.cons f,hp,hq⟩, by
    have : tuple_len V ⟨_,_,_,p,q,pr,qr⟩ < tuple_len V ⟨_,_,_,p.cons e,q.cons f,hp,hq⟩, by
    { dsimp [tuple_len,path.length], linarith, },
    by_cases zw : z = w,
    { induction zw,
      by_cases ef : e = f,
      { induction ef,
        cases is_forest_of_no_reduced_circuit  _ _ p q pr qr,
        refl, },
      { simpa using
          (congr_arg path.length (h _ _ (path.comp_reverse_is_reduced' p e q f hp hq ef))),
      } },
    { simpa using
        (congr_arg path.length (h _ _ (path.comp_reverse_is_reduced p e q f hp hq zw))), }, }
using_well_founded
{ dec_tac := `[assumption],
  rel_tac := λ _ _, `[exact ⟨_, measure_wf $ λ ⟨X,Y,p,q,pr,qr⟩, p.length⟩] }


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
