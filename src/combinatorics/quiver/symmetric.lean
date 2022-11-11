import combinatorics.quiver.basic
import combinatorics.quiver.path
import data.sum.basic
import logic.relation
import tactic.linarith

universes v u

namespace quiver

/-- A type synonym for the symmetrized quiver (with an arrow both ways for each original arrow).
    NB: this does not work for `Prop`-valued quivers. It requires `[quiver.{v+1} V]`. -/
@[nolint has_nonempty_instance]
def symmetrify (V) : Type u := V

instance symmetrify_quiver (V : Type u) [quiver V] : quiver (symmetrify V) :=
⟨λ a b : V, (a ⟶ b) ⊕ (b ⟶ a)⟩

variables (U V : Type*) [quiver.{u+1} U] [quiver.{v+1} V]

/-- A quiver `has_reverse` if we can reverse an arrow `p` from `a` to `b` to get an arrow
    `p.reverse` from `b` to `a`.-/
class has_reverse :=
(reverse' : Π {a b : V}, (a ⟶ b) → (b ⟶ a))

/-- Reverse the direction of an arrow. -/
def reverse {V} [quiver.{v+1} V] [has_reverse V] {a b : V} : (a ⟶ b) → (b ⟶ a) :=
  has_reverse.reverse'

/-- A quiver `has_involutive_reverse` if reversing twice is the identity.`-/
class has_involutive_reverse extends has_reverse V :=
(inv' : Π {a b : V} (f : a ⟶ b), reverse (reverse f) = f)

@[simp] lemma reverse_reverse {V} [quiver.{v+1} V] [h : has_involutive_reverse V]
  {a b : V} (f : a ⟶ b) : reverse (reverse f) = f := by apply h.inv'

variables {U V}

class prefunctor.preserves_reverse [has_reverse U] [has_reverse V] (φ : U ⟶q V) :=
(map_reverse' : ∀ {u v : U} (e : u ⟶ v), φ.map (reverse e) = reverse (φ.map e))

@[simp] lemma map_reverse  [has_reverse U] [has_reverse V] (φ : U ⟶q V) [φ.preserves_reverse]
  {u v : U} (e : u ⟶ v) : φ.map (reverse e) = reverse (φ.map e) :=
prefunctor.preserves_reverse.map_reverse' e

instance : has_reverse (symmetrify V) := ⟨λ a b e, e.swap⟩
instance : has_involutive_reverse (symmetrify V) :=
{ to_has_reverse := ⟨λ a b e, e.swap⟩,
  inv' := λ a b e, congr_fun sum.swap_swap_eq e }

@[simp] lemma symmetrify_reverse {a b : symmetrify V} (e : a ⟶ b) :
  reverse e = e.swap := rfl

/-- Shorthand for the "forward" arrow corresponding to `f` in `symmetrify V` -/
abbreviation hom.to_pos {X Y : V} (f : X ⟶ Y) :
  (quiver.symmetrify_quiver V).hom X Y := sum.inl f

/-- Shorthand for the "backward" arrow corresponding to `f` in `symmetrify V` -/
abbreviation hom.to_neg {X Y : V} (f : X ⟶ Y) :
  (quiver.symmetrify_quiver V).hom Y X := sum.inr f

/-- Reverse the direction of a path. -/
@[simp] def path.reverse [has_reverse V] {a : V} : Π {b}, path a b → path b a
| a path.nil := path.nil
| b (path.cons p e) := (reverse e).to_path.comp p.reverse

@[simp] lemma path.reverse_to_path [has_reverse V] {a b : V} (f : a ⟶ b) :
  f.to_path.reverse = (reverse f).to_path := rfl

@[simp] lemma path.reverse_comp [has_reverse V] {a b c : V} (p : path a b) (q : path b c) :
  (p.comp q).reverse = q.reverse.comp p.reverse := by
{ induction q, { simp, }, { simp [q_ih], }, }

@[simp] lemma path.reverse_reverse [h : has_involutive_reverse V] {a b : V} (p : path a b) :
  p.reverse.reverse = p := by
{ induction p,
  { simp, },
  { simp only [path.reverse, path.reverse_comp, path.reverse_to_path, reverse_reverse, p_ih],
    refl, }, }

namespace symmetrify

/-- The inclusion of a quiver in its symmetrification -/
def of : prefunctor V (symmetrify V) :=
{ obj := id,
  map := λ X Y f, sum.inl f }

/-- Given a quiver `V'` with reversible arrows, a prefunctor to `V'` can be lifted to one from
    `symmetrify V` to `V'` -/
def lift {V' : Type*} [quiver V'] [has_reverse V'] (φ : prefunctor V V') :
  prefunctor (symmetrify V) V' :=
{ obj := φ.obj,
  map := λ X Y f, sum.rec (λ fwd, φ.map fwd) (λ bwd, reverse (φ.map bwd)) f }

lemma lift_spec  (V' : Type*) [quiver V'] [has_reverse V'] (φ : prefunctor V V') :
  of.comp (lift φ) = φ :=
begin
  fapply prefunctor.ext,
  { rintro X, refl, },
  { rintros X Y f, refl, },
end

lemma lift_reverse  (V' : Type*) [quiver V'] [h : has_involutive_reverse V']
  (φ : prefunctor V V')
  {X Y : symmetrify V} (f : X ⟶ Y) :
  (lift φ).map (quiver.reverse f) = quiver.reverse ((lift φ).map f) :=
begin
  dsimp [lift], cases f,
  { simp only, refl, },
  { simp only, rw h.inv', refl, }
end

/-- `lift φ` is the only prefunctor extending `φ` and preserving reverses. -/
lemma lift_unique (V' : Type*) [quiver V'] [has_reverse V']
  (φ : prefunctor V V')
  (Φ : prefunctor (symmetrify V) V')
  (hΦ : of.comp Φ = φ)
  (hΦinv : ∀ {X Y : V} (f : X ⟶ Y), Φ.map (reverse f) = reverse (Φ.map f)) :
  Φ = lift φ :=
begin
  subst_vars,
  fapply prefunctor.ext,
  { rintro X, refl, },
  { rintros X Y f,
    cases f,
    { refl, },
    { dsimp [lift,of],
      convert hΦinv (sum.inl f), }, },
end

end symmetrify

namespace push

variables {W : Type*} (σ : V → W)

instance [has_reverse V] : has_reverse (push σ) :=
{ reverse' := λ a b F, by { cases F, constructor, apply reverse, exact F_f, } }

instance [h : quiver.has_involutive_reverse V] : quiver.has_involutive_reverse (push σ) :=
{ reverse' := λ a b F, by { cases F, constructor, apply reverse, exact F_f, },
  inv' :=  λ a b F, by
  { cases F, dsimp [reverse], congr, apply h.inv', } }

@[simp] lemma of_reverse [h : has_involutive_reverse V]  (X Y : V) (f : X ⟶ Y):
  (reverse $ ((of σ)).map f) = ((of σ)).map (reverse f) := rfl

end push


section connected_and_acyclic

open relation

variables {V} [has_involutive_reverse V]

inductive red.atomic_step {X: V} : path X X → path X X → Prop
| zz {Y : V} (f : X ⟶ Y) : red.atomic_step ((path.nil.cons f).cons (reverse f)) path.nil

inductive red.step {X Y : V} : path X Y → path X Y → Prop
| zz {Z : V} (pre : path X Z) {f g : path Z Z} (h : red.atomic_step f g) (suf : path Z Y) :
  red.step ((pre.comp f).comp suf) ((pre.comp g).comp suf)

abbreviation red.step_refl {X Y : V} (p q : path X Y) : Prop := refl_gen red.step p q
abbreviation red  {X Y : V}  (p q : path X Y) : Prop := refl_trans_gen (red.step) p q
abbreviation red.symm  {X Y : V}  (p q : path X Y) : Prop := join (red) p q

def path.is_reduced {X Y : V} (p : path X Y) := ∀ (q : path X Y), ¬ red.step p q


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

lemma nil_is_reduced {X : V} : (path.nil : path X X).is_reduced :=
begin
  rintro p h, rw step_iff at h,
  obtain ⟨_,_,_,_,_,h',h''⟩ := h,
  replace h' := congr_arg (path.length) h',
  simp only [path.length_nil, path.comp_cons, path.comp_nil, path.length_comp,
             path.length_cons] at h',
  linarith only [h'],
end

lemma exists_is_reduced {X Y : V} [∀ p : path X Y, decidable p.is_reduced] :
   ∀ (p : path X Y), ∃ (r : path X Y), (red p r ∧ r.is_reduced)
| p := if h : p.is_reduced then ⟨p, by {apply refl_trans_gen.refl}, h⟩ else by
  { dsimp [path.is_reduced] at h, push_neg at h,
    obtain ⟨q,qp⟩ := h,
    let : q.length < p.length := step_length_lt p q qp, -- hint for well-foundedness
    obtain ⟨r, rq, rred⟩ := exists_is_reduced q,
    refine ⟨r, _, rred⟩,
    exact refl_trans_gen.trans (refl_trans_gen.single qp) rq, }
using_well_founded
{ dec_tac := `[assumption],
  rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ (p : path X Y), p.length)⟩] }

end red

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
  { exact red.nil_is_reduced, },
  { exact hp.left, },
end

variable (V)

def is_forest := ∀ (X Y : V), subsingleton $ subtype { p : path X Y | p.is_reduced }

lemma no_reduced_circuit_of_no_cyclically_reduced_circuit
  (h : ∀ {X : V} (p : path X X), p.is_cyclically_reduced → p = path.nil) :
  ∀ {X : V} (p : path X X), p.is_reduced → p = path.nil := sorry

lemma no_reduced_circuit_iff_no_cyclically_reduced_circuit :
  (∀ {X : V} (p : path X X), p.is_cyclically_reduced → p = path.nil) ↔
  (∀ {X : V} (p : path X X), p.is_reduced → p = path.nil) :=
⟨no_reduced_circuit_of_no_cyclically_reduced_circuit V,
 λ h X p hp, h p (p.is_reduced_of_is_cyclically_reduced hp)⟩


-- ah it's not quite that: we need cyclically reduced for cycles
lemma is_forest_of_no_reduced_loops
  (h : ∀ (X : V), subsingleton $ subtype { p : path X X | p.is_reduced }) :
  ∀ (n : ℕ) {X Y : V} (p q : path X Y) (hp : p.is_reduced) (hq : q.is_reduced)
    (hl : p.length + q.length = n), p = q
| 0 X Y p q hp hq hl := by
  { simp at hl,
    let hpl := path.nil_of_length_zero _ hl.left,
    let hql := path.nil_of_length_zero _ hl.right, rw ←hql at hpl, simp at hpl, exact hpl, }
| (n+1) X Y p q hp hq hl := by sorry
-- if both p and q are reduced:
-- if they end with the same bit, one can reduce that bit and apply induction hypothesis
-- if they sartt with the same bit, one can reduce that bit and apply induction hyp
-- if neither, then their concatenation is

lemma is_forest_iff :
  is_forest V ↔ ∀ (X : V), subsingleton $ subtype { p : path X X | p.is_reduced } :=
begin
  split,
  { rintro h X,
    exact h X X, },
  { sorry, }
end

def is_connected := ∀ (X Y : V), nonempty $ path X Y

lemma is_connected_iff :
  is_connected V ↔ ∀ (X Y : V), nonempty $ subtype { p : path X Y | p.is_reduced } :=
begin
  classical,
  split,
  { rintro h X Y,
    obtain ⟨r,rred⟩ := red.exists_is_reduced (h X Y).some,
    exact ⟨⟨r,rred.right⟩⟩, },
  { rintro h X Y,
    exact ⟨(h X Y).some⟩, },
end

end connected_and_acyclic

end quiver
