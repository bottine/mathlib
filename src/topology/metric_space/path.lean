import data.real.ennreal
import data.real.nnreal
import data.set.intervals.basic
import topology.metric_space.emetric_space
import topology.metric_space.basic
import data.list.destutter

noncomputable theory

open_locale classical ennreal

open emetric nnreal set

-- TODO: allow `[emetric_space α]`
-- TODO: how to deal with paths defined non ICC intervals ?

namespace function

section length_on

variables {α β : Type*} [metric_space α]
variables (f : β → α)

def length_on : list β → nnreal
| list.nil      := 0
| [_]           := 0
| (a :: b :: l) := nndist (f a) (f b) + length_on (b :: l)

@[simp] lemma length_on_nil : f.length_on list.nil = 0 := rfl
@[simp] lemma length_on_cons_nil (b : β) : f.length_on [b] = 0 := rfl
@[simp] lemma length_on_cons_cons (a b : β) (l : list β) :
  f.length_on (a :: b :: l) = nndist (f a) (f b) + f.length_on (b :: l) := rfl

@[simp]
lemma length_on_append_cons_cons :
  ∀ (l : list β) (a b : β), f.length_on (l ++ [a, b]) = f.length_on (l ++ [a]) + nndist (f a) (f b)
| [] a b := by
  { simp only [list.nil_append, length_on_cons_cons,
                          length_on_cons_nil, add_zero, zero_add], }
| [x] a b := by
  { simp only [list.singleton_append, length_on_cons_cons,
                           length_on_cons_nil, add_zero], }
| (x :: y :: l) a b := by
  { simp only [list.cons_append, length_on_cons_cons],
    change y :: (l ++ [a]) with (y :: l) ++ [a],
    rw [add_assoc, ←length_on_append_cons_cons], refl, }

lemma length_on_le_length_on_cons (c : β) :
  ∀ (l : list β), f.length_on l ≤ (f.length_on $ c :: l)
| list.nil := by simp
| [a] := by simp
| (a :: b :: l) := by
  { simp only [length_on], rw ←add_assoc, apply add_le_add_right, apply le_add_left, refl, }

lemma length_on_cons_list_append_cons : ∀ (a : β) (l : list β) (z : β),
  f.length_on ([a] ++ l ++ [z]) = (list.map₂ (λ x y, nndist (f x) (f y)) ([a] ++ l) (l ++ [z])).sum
| a []  z := by
  { simp only [list.map₂, list.singleton_append, length_on_cons_cons,
               length_on_cons_nil, list.nil_append, list.sum_cons, list.sum_nil], }
| a [b] z := by -- **TODO** a simple simp works, but squeezing it doesn't :(
  { simp only [list.map₂, list.singleton_append, list.cons_append, length_on_cons_cons,
               length_on_cons_nil, add_zero, list.sum_cons, list.sum_nil, add_left_inj,
               eq_self_iff_true],
    simp only [list.map₂, list.nil_append, list.singleton_append, length_on_cons_cons,
               length_on_cons_nil, list.sum_cons, list.sum_nil], }
| a (b :: c :: l) z := by
  { simp only [list.map₂, list.nil_append, list.cons_append, length_on_cons_cons,
               list.sum_cons, add_right_inj],
    apply length_on_cons_list_append_cons, }

lemma length_on_le_length_on_append_left :
  ∀ (l l' : list β), f.length_on l ≤ f.length_on (l ++ l')
| []            _ := by simp only [length_on_nil, zero_le']
| [_]           _ := by simp only [length_on_cons_nil, zero_le']
| (_ :: _ :: _) _ := by
  { simp only [length_on_cons_cons, list.cons_append, add_le_add_iff_left],
    rw [←list.cons_append],
    apply length_on_le_length_on_append_left }

lemma length_on_le_length_on_append_right :
  ∀ (l l' : list β), f.length_on l' ≤ f.length_on (l ++ l')
| [] _ := by simp
| (a :: l) l' := by
  { transitivity' (f.length_on $ l ++ l'),
    apply length_on_le_length_on_append_right,
    apply length_on_le_length_on_cons, }

lemma length_on_drop_second_cons_le :
  ∀ (a b : β) (l : list β), f.length_on (a :: l) ≤ f.length_on (a :: b :: l)
| _ _ []  := by { simp only [length_on_cons_nil, zero_le'], }
| _ _ (c::l) := by
  { simp only [length_on_cons_cons, ←add_assoc, add_le_add_iff_right], apply nndist_triangle, }

lemma nndist_le_length_on_cons :
  ∀ (a : β) {b : β} {l : list β} (bl : b ∈ l), nndist (f a) (f b) ≤ f.length_on (a :: l)
| a b [] hb := by simpa using hb
| a b [x] hb := by
  { simp only [length_on_cons_cons, length_on_cons_nil, add_zero, list.mem_singleton] at hb ⊢,
    cases hb, refl, }
| a b (x :: y :: l) hb := by
  { simp only [length_on_cons_cons, list.mem_cons_iff] at hb ⊢,
    cases hb; cases hb,
    { simp only [le_add_iff_nonneg_right, zero_le'], },
    { cases hb, apply (nndist_triangle (f a) (f x) (f b)).trans,
      simp only [add_le_add_iff_left, le_add_iff_nonneg_right, zero_le'], },
    { apply (nndist_le_length_on_cons a hb).trans,
      apply (f.length_on_drop_second_cons_le a y l).trans,
      simp only [length_on_cons_cons, ←add_assoc, add_le_add_iff_right, nndist_triangle], } }


lemma nndist_le_length_on :
  ∀ {a b : β} {l : list β} (al : a ∈ l) (bl : b ∈ l), nndist (f a) (f b) ≤ f.length_on l
| a b [] ha hb := by simpa using ha
| a b (x :: l) ha hb := by
  { simp only [list.mem_cons_iff] at ha hb ⊢,
    cases ha; cases hb,
    { subst_vars, simp only [nndist_self, zero_le'], },
    { subst_vars, apply nndist_le_length_on_cons, exact hb, },
    { subst_vars, rw nndist_comm, apply nndist_le_length_on_cons, exact ha, },
    { apply (nndist_le_length_on ha hb).trans, apply length_on_le_length_on_cons, }, }

lemma length_on_destutter :
  ∀ l, f.length_on l = f.length_on (list.destutter (≠) l)
| [] := by { simp, }
| [_] := by { simp, }
| (a :: b :: l) := by
  { simp only [list.destutter_cons_cons, ite_not],
    split_ifs,
    { subst_vars,
      rw [length_on_cons_cons, length_on_destutter (b :: l)],
      simpa only [nndist_self, zero_add], },
    { cases l with c l,
      { simp, },
      { simp only [list.destutter'_cons, length_on_cons_cons, ite_not],
        split_ifs,
        { subst_vars,
          change list.destutter' ne c l with list.destutter ne (c :: l),
          rw length_on_cons_cons f,

          rw ←length_on_destutter, } } } }

lemma length_on_reverse : ∀ (l : list β), f.length_on l.reverse = f.length_on l
| [] := rfl
| [a] := rfl
| (a :: b :: l) := by
  { simp only [list.reverse_cons, list.append_assoc, list.singleton_append,
               length_on_append_cons_cons, length_on_cons_cons],
    rw ←list.reverse_cons, rw length_on_reverse, rw add_comm, rw nndist_comm, }

end length_on

section path_length

variables {α : Type*} [metric_space α] {s t : set ℝ}
variables (f : s → α) (l : list s)

/--
The path length of `f` is the supremum over all strictly increasing partitions `l`
of the length of `f` for `l`
-/
def path_length : ennreal :=
  ⨆ l ∈ {l : list s | l.pairwise (≤)}, f.length_on l

lemma path_length_mono (h : t ⊆ s) : (f ∘ inclusion h).path_length ≤ f.path_length := sorry

lemma path_length_comp (φ : t → s) :
  (f ∘ φ).path_length ≤ f.path_length := sorry

lemma path_length_reparametrize (φ : t → s) [monotone φ] [surjective φ] :
  (f ∘ φ).path_length = f.path_length := sorry

lemma path_length_reparametrize_anti (φ : t → s) [antitone φ] [surjective φ] :
  (f ∘ φ).path_length = f.path_length := sorry

lemma path_length_glue_split (x : ℝ) (xs : x ∈ s) : f.path_length =
  (f ∘ (inclusion (λ x h, h.1 : {y ∈ s | y ≤ x} ⊆ s))).path_length +
  (f ∘ (inclusion (λ x h, h.1 : {y ∈ s | y ≥ x} ⊆ s))).path_length := sorry

/--
A path is rectifiable if any of its restriction to a close interval has finite length
-/
def is_rectifiable := ∀ (a b : ℝ), ∃ (h : (Icc a b) ⊆ s), (f ∘ inclusion h).path_length ≠ ⊤


end path_length

end function
