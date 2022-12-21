import data.real.ennreal
import topology.metric_space.emetric_space

open emetric nnreal set

noncomputable theory

namespace function


variables {α β : Type*} [pseudo_emetric_space α]
variables (f : β → α)

@[simp] def dist_head : β → list β → ennreal
| _ [] := 0
| x (a :: _) := edist (f x) (f a)

lemma dist_head_le_append :
  ∀ (l : list β) (b : β) (l' : list β), f.dist_head b l ≤ f.dist_head b (l ++ l')
| [] _ _ := zero_le'
| (_::_) _ _ := le_refl _

lemma dist_head_triangle :
  ∀ (a b : β) (l : list β), f.dist_head a l ≤ edist (f a) (f b) + f.dist_head b l
| _ _ [] := zero_le'
| _ _ (_::_) := edist_triangle _ _ _


-- Maybe we should do `length_on + edist` rather than `edist + length_on`
-- to get better definitional behaviour?
@[simp] def length_on : list β → ennreal
| [] := 0
| [_] := 0
| (a::b::l) := edist (f a) (f b) + (length_on (b::l))

lemma length_on_pair (a b : β) : edist (f a) (f b) = f.length_on [a, b] :=
by simp only [length_on, add_zero]

lemma length_on_append_cons_cons :
   ∀ (l : list β) (a b : β), f.length_on (l ++ [a, b]) = f.length_on (l ++ [a]) + edist (f a) (f b)
| [] a b := by
  { simp only [length_on, list.nil_append, add_zero, zero_add], }
| [x] a b := by
  { simp only [length_on, list.singleton_append, add_zero], }
| (x :: y :: l) a b := by
  { simp only [length_on, list.cons_append, add_assoc],
    congr,
    simp only [←list.cons_append],
    apply length_on_append_cons_cons, }

lemma length_on_le_length_on_cons (c : β) (l : list β) : f.length_on l ≤ (f.length_on $ c :: l) :=
by { cases l, simp only [length_on, le_zero_iff], simp only [length_on], apply self_le_add_left _ _, }

lemma length_on_drop_second_cons_le :
  ∀ (a b : β) (l : list β), f.length_on (a :: l) ≤ f.length_on (a :: b :: l)
| _ _ []  := by
  { simp only [length_on, zero_le', dist_head, add_zero], }
| a b (c::l) := by
  { simp only [length_on, ←add_assoc],
    apply add_le_add_right (edist_triangle _ _ _) (f.length_on (c :: l)), }

lemma length_on_append : ∀ l l', f.length_on l + f.length_on l' ≤ f.length_on (l ++ l')
| [] l' := by
  { rw [list.nil_append, length_on, zero_add], exact le_refl (f.length_on l'), }
| [a] l' := by
  { rw [list.singleton_append, length_on, zero_add],
    apply length_on_le_length_on_cons, }
| (a :: b :: l) l' := by
  { rw [list.cons_append, length_on, add_assoc],
    refine add_le_add_left (length_on_append (b::l) l') _, }

lemma length_on_reverse : ∀ (l : list β), f.length_on l.reverse = f.length_on l
| [] := rfl
| [a] := rfl
| (a :: b :: l) := by
  { simp only [length_on_append_cons_cons, ←length_on_reverse (b :: l), list.reverse_cons,
               list.append_assoc, list.singleton_append, length_on],
    rw [add_comm, edist_comm], }

lemma length_on_map {γ : Type*} (φ : γ → β) :
  ∀ (l : list γ), f.length_on (l.map φ) = (f ∘ φ).length_on l
| [] := by { simp only [length_on, list.map_nil], }
| [a] := by { simp only [length_on, list.map], }
| (a :: b :: l)  := by { simp only [length_on, list.map, comp_app, ←length_on_map (b::l)], }

lemma length_on_le_append_singleton_append :
  ∀ (l : list β) (x : β) (l' : list β), f.length_on (l ++ l') ≤ f.length_on (l ++ [x] ++ l')
| [] x l' := by { apply length_on_le_length_on_cons, }
| [a] x l' := by { apply length_on_drop_second_cons_le, }
| (a :: b :: l) x l' := by
  { change a :: b :: l ++ l' with a :: b :: (l ++ l'),
    change a :: b :: l ++ [x] ++ l' with a :: b :: (l ++ [x] ++ l'),
    simp only [length_on],
    apply add_le_add_left _ (edist (f a) (f b)),
    exact length_on_le_append_singleton_append (b :: l) x l', }

lemma length_on_append_singleton_append :
  ∀ (l : list β) (x : β) (l' : list β),
    f.length_on (l ++ [x] ++ l') = f.length_on (l ++ [x]) + f.length_on ([x] ++ l')
| [] x l' := by { simp only [length_on, list.nil_append, zero_add]}
| [a] x l' := by
  { simp only [length_on, list.singleton_append, list.cons_append, add_zero, eq_self_iff_true,
               list.nil_append], }
| (a :: b :: l) x l' := by
  { simp only [length_on, list.cons_append, list.append_assoc, list.singleton_append, add_assoc],
    congr,
    simp_rw [←list.cons_append b l, ←@list.singleton_append _ x l',←list.append_assoc],
    exact length_on_append_singleton_append (b::l) x l', }

lemma length_on_mono : ∀ {l l'}, l <+ l' → f.length_on l ≤ f.length_on l' := sorry

lemma _root_.list.pair_mem_list {a b : β} :
  ∀ (l : list β), a ∈ l → b ∈ l → a = b ∨ [a,b] <+ l ∨ [b,a] <+ l
| [] al bl := by { simpa only [list.not_mem_nil] using al, }
| (x::l) al bl := by
  { simp only [list.mem_cons_iff] at al bl, cases al; cases bl,
    { left, exact al.trans bl.symm, },
    { rw al, right, left, apply list.sublist.cons2,
      simpa only [list.singleton_sublist] using bl, },
    { rw bl, right,  right, apply list.sublist.cons2,
      simpa only [list.singleton_sublist] using al, },
    { rcases _root_.list.pair_mem_list l al bl with h|ab|ba,
      { left, exact h, },
      { right, left, constructor, exact ab, },
      { right, right, constructor, exact ba, }, }, }

lemma edist_le_length_on_of_mem {a b : β} {l : list β} (al : a ∈ l) (bl : b ∈ l) :
  edist (f a) (f b) ≤ f.length_on l :=
begin
  rcases l.pair_mem_list al bl with rfl|ab|ba,
  { simp only [edist_self, zero_le'], },
  { rw [length_on_pair], exact f.length_on_mono ab, },
  { rw [edist_comm, length_on_pair], exact f.length_on_mono ba, }
end




end function
