import data.real.ennreal
import topology.metric_space.emetric_space
import .path_preliminaries
import topology.instances.ennreal

open emetric nnreal set ennreal

namespace function

section length_on

variables {α β : Type*} [pseudo_emetric_space α]
variables (f : β → α)

-- This definition yields a very messy term and troubles down the road!
/-@[simp] def length_on : list β → ennreal
| list.nil := 0
| (list.cons _ list.nil) := 0
| (a::b::l) := edist (f a) (f b) + (length_on (b::l))
-/

-- definition 'length_on' depends on 'ennreal.canonically_ordered_comm_semiring
-- so says lean
noncomputable def length_on : list β → ennreal :=
list.rec 0
  (λ (a : β) (l : list β) (ih : ennreal),
      list.rec 0 (λ (b : β) (l : list β) (ih' : ennreal), edist (f a) (f b) + ih) l)

lemma length_on_nil : f.length_on list.nil = 0 := rfl
lemma length_on_singleton (a : β) : f.length_on [a] = 0 := rfl
lemma length_on_cons_cons (a b : β) (l : list β) :
  f.length_on (a::b::l) = edist (f a) (f b) + f.length_on (b::l) := rfl

lemma length_on_pair (a b : β) : edist (f a) (f b) = f.length_on [a, b] :=
by simp only [length_on_cons_cons, length_on_singleton, add_zero]

lemma length_on_append_cons_cons :
   ∀ (l : list β) (a b : β), f.length_on (l ++ [a, b]) = f.length_on (l ++ [a]) + edist (f a) (f b)
| [] a b := by
  { simp only [length_on, list.nil_append, add_zero, zero_add], }
| [x] a b := by
  { simp only [length_on, list.singleton_append, add_zero], }
| (x :: y :: l) a b := by
  { simp only [length_on_cons_cons, list.cons_append, add_assoc],
    congr,
    simp only [←list.cons_append],
    apply length_on_append_cons_cons, }

lemma length_on_le_length_on_cons (c : β) (l : list β) : f.length_on l ≤ (f.length_on $ c :: l) :=
by { cases l, simp only [length_on, le_zero_iff], simp only [length_on], apply self_le_add_left _ _, }

lemma length_on_drop_second_cons_le :
  ∀ (a b : β) (l : list β), f.length_on (a :: l) ≤ f.length_on (a :: b :: l)
| _ _ []  := by
  { apply length_on_le_length_on_cons, }
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
               list.append_assoc, list.singleton_append, length_on_cons_cons],
    rw [add_comm, edist_comm], }

lemma length_on_map {γ : Type*} (φ : γ → β) :
  ∀ (l : list γ), f.length_on (l.map φ) = (f ∘ φ).length_on l
| [] := by { simp only [length_on, list.map_nil], }
| [a] := by { simp only [length_on, list.map], }
| (a :: b :: l)  := by
  { simp only [length_on_cons_cons, list.map, comp_app, ←length_on_map (b::l)], }

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
  { simp only [length_on_cons_cons, list.cons_append, list.append_assoc, list.singleton_append,
    add_assoc],
    congr,
    simp_rw [←list.cons_append b l, ←@list.singleton_append _ x l',←list.append_assoc],
    exact length_on_append_singleton_append (b::l) x l', }

lemma length_on_mono' :
  ∀ {l l' : list β}, l <+ l' → ∀ x, f.length_on (x::l) ≤ f.length_on (x::l')
| _ _ list.sublist.slnil             x := by { simp only [length_on, le_zero_iff], }
| _ _ (list.sublist.cons  l₁ l₂ a s) x :=
  (f.length_on_drop_second_cons_le x a l₁).trans $ add_le_add_left (length_on_mono' s a) _
| _ _ (list.sublist.cons2 l₁ l₂ a s) x := add_le_add_left (length_on_mono' s a) _

lemma length_on_mono : ∀ {l l' : list β}, l <+ l' → f.length_on l ≤ f.length_on l'
| _ _ list.sublist.slnil             := by { simp only [length_on, le_zero_iff], }
| _ _ (list.sublist.cons  l₁ l₂ a s) :=
  (f.length_on_le_length_on_cons a l₁).trans $ f.length_on_mono' s a
| _ _ (list.sublist.cons2 l₁ l₂ a s) := f.length_on_mono' s a

lemma edist_le_length_on_of_mem {a b : β} {l : list β} (al : a ∈ l) (bl : b ∈ l) :
  edist (f a) (f b) ≤ f.length_on l :=
begin
  rcases l.pair_mem_list al bl with rfl|ab|ba,
  { simp only [edist_self, zero_le'], },
  { rw [length_on_pair], exact f.length_on_mono ab, },
  { rw [edist_comm, length_on_pair], exact f.length_on_mono ba, }
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
noncomputable def path_length : ennreal :=
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
    rintro x xm y my, apply le_trans xm my, }, -- `xm.trans my` doesn't work
end

/--
A path is rectifiable if any of its restriction to a close interval has finite length
-/
def is_rectifiable :=
  ∀ (a b : β), (f ∘ (λ x : Icc a b, x.val)).path_length ≠ ⊤

end path_length



end function
