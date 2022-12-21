import data.real.ennreal
import data.real.nnreal
import data.set.intervals.basic
import topology.metric_space.emetric_space
import topology.metric_space.basic
import data.list.destutter
import topology.instances.ennreal
import .path_preliminaries

open emetric nnreal set

noncomputable theory

namespace function

section length_on

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


@[simp] def length_on : list β → ennreal
| list.nil := 0
| (a :: l) := f.dist_head a l + length_on l

lemma length_on_nil : f.length_on list.nil = 0 := rfl
lemma length_on_cons_nil (b : β) : f.length_on [b] = 0 := by simp_rw [length_on, dist_head, add_zero]
lemma length_on_cons_cons (a b : β) (l : list β) :
  f.length_on (a :: b :: l) = edist (f a) (f b) + f.length_on (b :: l) := rfl

lemma length_on_cons_eq_dist_head_add_length_on (a : β) (l : list β) :
  f.length_on (a :: l) = f.dist_head a l + f.length_on l := rfl

lemma length_on_append_cons_cons :
   ∀ (l : list β) (a b : β), f.length_on (l ++ [a, b]) = f.length_on (l ++ [a]) + edist (f a) (f b)
| [] a b := by
  { simp only [length_on, dist_head, list.nil_append, add_zero, zero_add], }
| [x] a b := by
  { simp only [length_on, dist_head, list.singleton_append, add_zero], }
| (x :: y :: l) a b := by
  { simp only [length_on, dist_head, list.cons_append],
    change edist (f x) (f y) + length_on f (y :: (l ++ [a, b])) =
           edist (f x) (f y) + length_on f (y :: l ++ [a]) + edist (f a) (f b),
    rw [add_assoc, ←length_on_append_cons_cons], refl, }

lemma length_on_le_length_on_cons (c : β) (l : list β) : f.length_on l ≤ (f.length_on $ c :: l) :=
self_le_add_left _ _

lemma length_on_drop_second_cons_le :
  ∀ (a b : β) (l : list β), f.length_on (a :: l) ≤ f.length_on (a :: b :: l)
| _ _ []  := by
  { simp only [length_on, zero_le', dist_head, add_zero], }
| a b (c::l) := by
  { simp_rw [length_on_cons_cons, ←add_assoc],
    apply add_le_add_right _ (f.length_on (c :: l)),
    apply edist_triangle, }

lemma edist_mem_le_length_on_cons :
  ∀ (a : β) {b : β} {l : list β} (bl : b ∈ l), edist (f a) (f b) ≤ f.length_on (a :: l)
| a b [] hb := (list.not_mem_nil _ hb).elim
| a b [x] hb := by
  { simp_rw [length_on_cons_cons, length_on_cons_nil, add_zero, list.mem_singleton] at hb ⊢,
    cases hb, exact le_refl _, }
| a b (x :: y :: l) hb := by
  { simp_rw [length_on_cons_cons, list.mem_cons_iff] at hb ⊢,
    cases hb; cases hb,
    { apply self_le_add_right _ _, },
    { cases hb,
      apply (edist_triangle (f a) (f x) (f b)).trans,
      rw ←add_assoc,
      apply self_le_add_right _ (length_on f (b :: l)), },
    { apply (edist_mem_le_length_on_cons a hb).trans,
      apply (f.length_on_drop_second_cons_le a y l).trans,
      rw [length_on_cons_cons, ←add_assoc],
      apply add_le_add_right _ (length_on f (y :: l)),
      apply edist_triangle, } }

lemma edist_le_length_on :
  ∀ {a b : β} {l : list β} (al : a ∈ l) (bl : b ∈ l), edist (f a) (f b) ≤ f.length_on l
| a b [] ha hb := (list.not_mem_nil _ ha).elim
| a b (x :: l) ha hb := by
  { simp only [list.mem_cons_iff] at ha hb ⊢,
    cases ha; cases hb,
    { subst_vars, simp only [edist_self, zero_le'], },
    { subst_vars, apply edist_mem_le_length_on_cons, exact hb, },
    { subst_vars, rw edist_comm, apply edist_mem_le_length_on_cons, exact ha, },
    { apply (edist_le_length_on ha hb).trans, apply length_on_le_length_on_cons, }, }

lemma length_on_append : ∀ l l', f.length_on l + f.length_on l' ≤ f.length_on (l ++ l')
| [] l' := by
  { simp only [list.nil_append, length_on_nil, zero_add], exact le_refl _, }
| [a] l' := by
  { simp only [list.singleton_append, length_on_cons_nil, zero_add],
    apply length_on_le_length_on_cons, }
| (a :: b :: l) l' := by
  { simp only [list.cons_append, length_on_cons_cons, add_assoc],
    refine add_le_add_left _ _,
    apply length_on_append, }

lemma length_on_le_length_on_append_left
  (l l' : list β) : f.length_on l ≤ f.length_on (l ++ l') :=
le_trans (self_le_add_right _ _) (f.length_on_append l l')

lemma length_on_le_length_on_append_right
  (l l' : list β) : f.length_on l' ≤ f.length_on (l ++ l') :=
le_trans (self_le_add_left _ _) (f.length_on_append l l')

lemma length_on_reverse : ∀ (l : list β), f.length_on l.reverse = f.length_on l
| [] := rfl
| [a] := rfl
| (a :: b :: l) := by
  { simp_rw [list.reverse_cons, list.append_assoc, list.singleton_append,
               length_on_append_cons_cons, length_on_cons_cons,
               ←list.reverse_cons, length_on_reverse, add_comm, edist_comm], }

lemma length_on_map {γ : Type*} (φ : γ → β) :
  ∀ (l : list γ), f.length_on (l.map φ) = (f ∘ φ).length_on l
| [] := by { simp only [list.map_nil, length_on_nil], }
| [a] := by { simp only [list.map, length_on_cons_nil], }
| (a :: b :: l)  := by
  { simp_rw [list.map, length_on_cons_cons, comp_apply, ←length_on_map, list.map], }

lemma length_on_le_append_singleton_append :
  ∀ (l : list β) (x : β) (l' : list β), f.length_on (l ++ l') ≤ f.length_on (l ++ [x] ++ l')
| [] x l' := by { apply length_on_le_length_on_cons, }
| [a] x l' := by { apply length_on_drop_second_cons_le, }
| (a :: b :: l) x l' := by
  { change a :: b :: l ++ l' with a :: b :: (l ++ l'),
    change a :: b :: l ++ [x] ++ l' with a :: b :: (l ++ [x] ++ l'),
    rw [length_on_cons_cons, length_on_cons_cons],
    apply add_le_add_left _ (edist (f a) (f b)),
    exact length_on_le_append_singleton_append (b :: l) x l', }

lemma length_on_append_singleton_append :
  ∀ (l : list β) (x : β) (l' : list β),
    f.length_on (l ++ [x] ++ l') = f.length_on (l ++ [x]) + f.length_on ([x] ++ l')
| [] x l' := by { simp only [list.nil_append, length_on_cons_nil, zero_add], }
| [a] x l' := by
  { simp only [length_on, dist_head, list.cons_append, add_zero, list.nil_append], }
| (a :: b :: l) x l' := by
  { simp only [list.cons_append, list.append_assoc, list.singleton_append, length_on_cons_cons],
    have : b :: (l ++ x :: l') = (b :: l) ++ [x] ++ l', by simp,
    rw [this, length_on_append_singleton_append, add_assoc], refl,  }

lemma length_on_mono' :
  ∀ l l', l <+ l' → (∀ x, f.dist_head x l + f.length_on l ≤ f.dist_head x l' + f.length_on l') :=
begin
  rintro l l' ll',
  induction ll' with l l' b ll' ih l l' b ll' ih,
  { simp only [dist_head, length_on_nil, add_zero, le_zero_iff, eq_self_iff_true,
               implies_true_iff], },
  { rintro x,
    apply (ih x).trans,
    exact length_on_drop_second_cons_le f _ _ _, },
  { rintro x, specialize ih b,
    refine add_le_add_left _ _, exact ih, }
end

lemma length_on_mono : ∀ l l', l <+ l' → f.length_on l ≤ f.length_on l' :=
begin
  rintro l l' ll',
  cases l',
  { simp only [length_on_nil, le_zero_iff, list.sublist_nil_iff_eq_nil] at ll' ⊢,
    cases ll',
    refl, },
  { let := f.length_on_mono' _ _ ll' l'_hd,
    simp only [length_on, dist_head, edist_self, zero_add] at this ⊢,
    apply le_trans _ this,
    refine self_le_add_left _ _, }
end

end length_on

section path_length

variables {α : Type*} [pseudo_emetric_space α]
  {β : Type*} [linear_order β]
  {γ : Type*} [linear_order γ]
variables (f : β → α) (l : list β)

/--
The path length of `f` is the supremum over all strictly increasing partitions `l`
of the length of `f` for `l`
-/
def path_length : ennreal :=
  ⨆ l ∈ {l : list β | l.pairwise (≤)}, f.length_on l

def sorted_list_nonempty : set.nonempty {l : list β | l.pairwise (≤)} := ⟨[],list.pairwise.nil⟩

lemma path_length_comp_mono (φ : γ → β) (mφ : monotone φ) :
  (f ∘ φ).path_length ≤ f.path_length :=
begin
  simp only [path_length, supr₂_le_iff, ←f.length_on_map φ],
  rintro l ls,
  exact @le_supr₂ _ _ _ _ (λ l H, f.length_on l) (l.map φ) (list.pairwise.map φ mφ ls),
end

lemma path_length_comp_anti (φ : γ → β) (mφ : antitone φ) :
  (f ∘ φ).path_length ≤ f.path_length :=
begin
  simp only [path_length, supr₂_le_iff, ←f.length_on_map φ],
  rintro l ls,
  rw [←f.length_on_reverse, ←list.map_reverse],
  refine @le_supr₂ _ _ _ _  (λ l H, f.length_on l) _ _,
  apply list.pairwise.map φ _ (list.pairwise_reverse.mpr ls),
  rintro a b h, exact mφ h,
end

lemma path_length_reparametrize_mono (φ : γ → β) (mφ : monotone φ) (sφ : surjective φ) :
  (f ∘ φ).path_length = f.path_length :=
begin
  apply le_antisymm,
  apply f.path_length_comp_mono φ mφ,

  obtain ⟨ψ,φψ⟩ := sφ.has_right_inverse,

  convert (f ∘ φ).path_length_comp_mono ψ (right_inverse_monotone φ mφ ψ φψ),
  ext x,
  simp only [comp_app, φψ x],
end

lemma path_length_reparametrize_anti (φ : γ → β) (mφ : antitone φ) (sφ : surjective φ) :
  (f ∘ φ).path_length = f.path_length :=
begin
  apply le_antisymm,
  apply f.path_length_comp_anti φ mφ,

  obtain ⟨ψ,φψ⟩ := sφ.has_right_inverse,

  convert (f ∘ φ).path_length_comp_anti ψ (right_inverse_antitone φ mφ ψ φψ),
  ext x,
  simp only [comp_app, φψ x],
end

set_option profiler true

/-- Statement ~copied from Gouezel's bounded variation code.
If `sl sr` are two subsets of `s`, `sl` to the left of `sr` the sum of the restricted lengths
is less or equal than the length.
-/
-- Probably deserves specializations for intervals
lemma path_length_ge_parts (l r : set β) (lr : ∀ x ∈ l, ∀ y ∈ r, x ≤ y) :
  (f ∘ (coe : subtype l → β)).path_length
  + (f ∘ (coe : subtype r → β)).path_length ≤ (f.path_length) :=
begin
  apply ennreal.bsupr_add_bsupr_le sorted_list_nonempty sorted_list_nonempty,
  rintro left lefts right rights,
  simp_rw [←length_on_map f coe],
  apply (f.length_on_append _ _).trans,
  dsimp only [path_length],
  refine @le_supr₂ _ _ _ _ (λ l H, f.length_on l) _ _,
  rw [mem_set_of, list.pairwise_append],
  refine ⟨list.pairwise.map _ (λ a b h, h) lefts,
          list.pairwise.map _ (λ a b h, h) rights,
          λ x xleft y yright, _⟩,
  simp only [list.mem_map, subtype.exists, subtype.coe_mk, exists_and_distrib_right,
             exists_eq_right] at xleft yright,
  obtain ⟨xl,xleft⟩ := xleft,
  obtain ⟨yr,yright⟩ := yright,
  exact lr x xl y yr,
end

lemma path_length_glue_split (m : β) :
  f.path_length = (f ∘ (coe : {x // x ≤ m} → β)).path_length
                + (f ∘ (coe : {x // m ≤ x} → β)).path_length :=
begin
  dsimp only [path_length],
  apply le_antisymm,
  { rw supr₂_le_iff,
    rintro l ls,
    rw ←list.take_while_append_drop (≤m) l,
    apply (length_on_le_append_singleton_append f _ m _).trans,
    rw length_on_append_singleton_append,
    refine add_le_add _ _,
    { transitivity' (f ∘ coe).length_on (l.take_while_subtype m ++ [⟨m,le_refl m⟩]),
      { rw [←f.length_on_map coe, list.map_append, list.take_while_subtype_map_coe],
        simp only [list.map, subtype.coe_mk], exact le_refl _, },
      { refine @le_supr₂ _ _ _ _ (λ l H, length_on (f ∘ coe) l) _ _,
        simp only [list.pairwise_append, mem_set_of_eq, list.mem_singleton],
        refine ⟨list.take_while_subtype_pairwise_le _ _, list.pairwise_singleton _ _, _⟩,
        rintro y yl _ rfl,
        exact list.take_while_subtype_le_base m l y yl, }, },
    { transitivity' (f ∘ coe).length_on
        ([(⟨m,le_refl m⟩ : {x // m ≤ x})] ++ (l.drop_while_subtype_ge m ls)),
      { rw [←f.length_on_map coe, list.map_append, list.drop_while_subtype_ge_map_coe],
        simp only [list.map, subtype.coe_mk], exact le_refl _, },
      { refine @le_supr₂ _ _ _ _ (λ l H, length_on (f ∘ coe) l) _ _,
        simp only [list.singleton_append, mem_set_of_eq, list.pairwise_cons,
                   subtype.mk_le_mk],
        refine ⟨list.drop_while_subtype_ge_ge_base _ _ _,
                list.drop_while_subtype_ge_pairwise_le _ _ _⟩, }, }, },
  { apply path_length_ge_parts,
    rintro x xm y my, apply le_trans, exact xm, exact my, }, -- `xm.trans my` doesn't work
end

/--
A path is rectifiable if any of its restriction to a close interval has finite length
-/
def is_rectifiable :=
  ∀ (a b : β), (f ∘ (λ x : Icc a b, x.val)).path_length ≠ ⊤

end path_length

end function
