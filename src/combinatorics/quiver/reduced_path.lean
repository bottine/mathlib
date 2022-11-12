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

inductive red.atomic_step {X: V} : path X X → path X X → Prop
| zz {Y : V} (f : X ⟶ Y) : red.atomic_step ((path.nil.cons f).cons (reverse f)) path.nil

inductive red.step {X Y : V} : path X Y → path X Y → Prop
| zz {Z : V} (pre : path X Z) {f g : path Z Z} (h : red.atomic_step f g) (suf : path Z Y) :
  red.step ((pre.comp f).comp suf) ((pre.comp g).comp suf)

abbreviation red.step_refl {X Y : V} (p q : path X Y) : Prop := refl_gen red.step p q
abbreviation red  {X Y : V}  (p q : path X Y) : Prop := refl_trans_gen (red.step) p q
abbreviation red.symm  {X Y : V}  (p q : path X Y) : Prop := join (red) p q


namespace red

lemma atomic_step_iff {X : V} (p q : path X X) :
  atomic_step p q ↔ ∃ (Y) (f : X ⟶ Y), p = ((path.nil.cons f).cons (reverse f)) ∧ q = path.nil :=
begin
  split,
  { rintro F, cases F with Y f, exact ⟨Y,f,rfl,rfl⟩, },
  { rintro ⟨Y,f,rfl,rfl⟩, constructor, },
end

lemma step_iff {X Y : V} (p q : path X Y) :
  step p q ↔ ∃ (Z W : V) (pre : path X Z) (f : Z ⟶ W) (suf : path Z Y),
               p = (pre.comp ((path.nil.cons f).cons (reverse f))).comp suf ∧ q = pre.comp suf :=
begin
  split,
  { rintro FS, cases FS with Z pre p q F suf, rw atomic_step_iff at F,
    rcases F with ⟨W,f,rfl,rfl⟩, exact ⟨Z,W,pre,f,suf,rfl,rfl⟩, },
  { rintro ⟨Z,W,pre,f,suf,rfl,rfl⟩,
    have : pre.comp suf = (pre.comp (path.nil)).comp suf, by simp,
    rw this,
    constructor, constructor, },
end

lemma step_length_lt {X Y : V} (p q : path X Y) : red.step p q → q.length < p.length :=
begin
  rintro FS, rw step_iff at FS,
  obtain ⟨Z,W,pre,f,suf,rfl,rfl⟩ := FS,
  simp only [path.length_comp, path.comp_cons, path.comp_nil, path.length_cons],
  linarith only [],
end

end red

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
  rintro p h, rw red.step_iff at h,
  obtain ⟨_,_,_,_,_,h',h''⟩ := h,
  replace h' := congr_arg (path.length) h',
  simp only [path.length_nil, path.comp_cons, path.comp_nil, path.length_comp,
             path.length_cons] at h',
  linarith only [h'],
end

lemma is_not_reduced_iff {X Y : V} (p : path X Y) : ¬ p.is_reduced ↔
  ∃ (Z W : V) (pre : path X Z) (f : Z ⟶ W) (suf : path Z Y),
    p = (pre.comp ((path.nil.cons f).cons (reverse f))).comp suf :=
begin
  dsimp [path.is_reduced], push_neg,
  simp_rw red.step_iff,
  split,
  { rintro ⟨_,Z,W,pre,f,suf,rfl, rfl⟩, exact ⟨Z,W,pre,f,suf,rfl⟩, },
  { rintro ⟨Z,W,pre,f,suf,rfl, rfl⟩, exact ⟨pre.comp suf, Z,W,pre,f,suf,rfl, rfl⟩, },
end


def path.shift_cons {X Y : V} (p : path X Y) (e : Y ⟶ X) : path Y Y := e.to_path.comp p

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

def is_forest := ∀ (X Y : V) (p q : path X Y), p.is_reduced → q.is_reduced → p = q

lemma no_reduced_circuit_of_no_cyclically_reduced_circuit
  (h : ∀ {X : V} (p : path X X), p.is_cyclically_reduced → p = path.nil) :
  ∀ {X : V} (p : path X X), p.is_reduced → p = path.nil := sorry

lemma no_reduced_circuit_iff_no_cyclically_reduced_circuit :
  (∀ {X : V} (p : path X X), p.is_cyclically_reduced → p = path.nil) ↔
  (∀ {X : V} (p : path X X), p.is_reduced → p = path.nil) :=
⟨no_reduced_circuit_of_no_cyclically_reduced_circuit V,
 λ h X p hp, h p (p.is_reduced_of_is_cyclically_reduced hp)⟩

lemma is_forest_of_no_reduced_loops
  (h : ∀ (X : V) (p : path X X) (hp : p.is_reduced), p = path.nil ) :
  ∀ {X Y : V} (p q : path X Y) (hp : p.is_reduced) (hq : q.is_reduced), p = q
| _ _ (path.nil) (path.nil) hp hq := rfl
| _ _ (path.cons p e) (path.nil) hp hq := h _ _ hp
| _ _ (path.nil) (path.cons q f) hp hq := (h _ _ hq).symm
| _ _ (@path.cons _ _ x z y p e) (@path.cons _ _ _ w _  q f) hp hq := by
  { by_cases zw : z = w,
    { induction zw,
      by_cases ef : e = f,
      { induction ef,
        have : q.is_reduced := sorry,
        have : p.is_reduced := sorry,
        have : p = q, by sorry, -- by induction hypothesis
        induction this, refl, },
      { -- `e ≠ f` means `(p.cons e).comp (q.cons f).reverse` is reduced
        have : ((p.cons e).comp (q.cons f).reverse).is_reduced := sorry,

      } }, }

lemma is_forest_iff :
  is_forest V ↔ ∀ (X : V) (p : path X X), p.is_reduced → p = path.nil :=
begin
  split,
  { rintro h X p hp, exact h X X p (path.nil) hp nil_is_reduced, },
  { sorry  }
end

def is_connected := ∀ (X Y : V), nonempty (path X Y)

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
