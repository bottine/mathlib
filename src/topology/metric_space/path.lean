import data.real.ennreal
import data.real.nnreal
import data.set.intervals.basic
import topology.metric_space.emetric_space
import topology.metric_space.basic
import data.list.destutter
import topology.instances.ennreal

noncomputable theory

open_locale classical ennreal

open emetric nnreal set

section preliminaries

variables {α : Type*} (x : α)


lemma subtype.map_id_comp_id (α : Type*) (r s t : α → Prop)
  (rs : ∀ x, r x → s x) (st : ∀ x, s x → t x) :
  (subtype.map id st) ∘ (subtype.map id rs) = (subtype.map id $ λ x, (st x) ∘ (rs x)) :=
funext (λ _, rfl)

lemma subtype.coe_comp_map_id (α : Type*) (r s : α → Prop)
  (rs : ∀ x, r x → s x) :
  coe ∘ (subtype.map id rs) = (coe : (subtype r) → α) :=
funext (λ _, rfl)

def list.take_while_subtype [preorder α] (l : list α) : list (subtype (≤x)) :=
(l.take_while (≤x)).attach.map $ subtype.map id $ λ y, list.mem_take_while_imp

lemma list.take_while_subtype_map_coe [preorder α] (l : list α) :
  (l.take_while_subtype x).map coe = l.take_while (≤x) :=
begin
  dsimp [list.take_while_subtype],
  simp only [list.map_map],
  apply list.attach_map_coe,
end

lemma list.pairwise_le_drop_while_le_not_le  [preorder α] :
  ∀ (l : list α) (h : l.pairwise (≤)) (y : α), y ∈ l.drop_while (≤x) → ¬y ≤ x
| [] h y hy := by { simp only [list.drop_while, list.not_mem_nil] at hy, exact hy.elim }
| (a::l) h y hy := by
  { dsimp [list.drop_while] at hy,
    simp only [list.pairwise_cons] at h,
    split_ifs at hy with ax nax,
    { exact list.pairwise_le_drop_while_le_not_le l h.right y hy, },
    { cases hy,
      { cases hy, exact ax},
      { rintro yx, exact ax ((h.left y hy).trans yx), }, }, }

def list.drop_while_subtype [preorder α] (l : list α) (h : l.pairwise (≤)) : list (subtype (λ y, ¬ y≤x)) :=
(l.drop_while (≤x)).attach.map $ subtype.map id (λ y, l.pairwise_le_drop_while_le_not_le x h y)

def list.drop_while_subtype_ge [linear_order α] (l : list α) (h : l.pairwise (≤)) :
  list (subtype (λ y, x≤y)) :=
(l.drop_while_subtype x h).map $ subtype.map id $ λ y h', @le_of_not_le α _ y x h'

lemma list.drop_while_subtype_ge_map_coe [linear_order α] (l : list α)(h : l.pairwise (≤)) :
  (l.drop_while_subtype_ge x h).map coe = l.drop_while (≤x) :=
begin
  dsimp [list.drop_while_subtype_ge, list.drop_while_subtype],
  simp [list.map_map, subtype.map_id_comp_id, subtype.coe_comp_map_id],
  finish,
end

end preliminaries

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

  -- Yael should know a lemma for this
  obtain ⟨ψ,φψ⟩ := sφ.has_right_inverse,
  have mψ : monotone ψ := by
  { rintro x y l,
    have := le_total (ψ x) (ψ y),
    cases this,
    { exact this, },
    { let := mφ (this),
      rw [φψ x, φψ y] at this,
      cases le_antisymm l this, refl, } },

  convert (f ∘ φ).path_length_comp_mono ψ mψ,
  ext x,
  simp only [comp_app, φψ x],
end

lemma path_length_reparametrize_anti (φ : γ → β) (mφ : antitone φ) (sφ : surjective φ) :
  (f ∘ φ).path_length = f.path_length :=
begin
  apply le_antisymm,
  apply f.path_length_comp_anti φ mφ,

  -- Yael should know a lemma for this
  obtain ⟨ψ,φψ⟩ := sφ.has_right_inverse,
  have mψ : antitone ψ := by
  { rintro x y l,
    have := le_total (ψ y) (ψ x),
    cases this,
    { exact this, },
    { let := mφ (this),
      rw [φψ x, φψ y] at this,
      cases le_antisymm l this, refl, } },

  convert (f ∘ φ).path_length_comp_anti ψ mψ,
  ext x,
  simp only [comp_app, φψ x],
end

/-- Statement ~copied from Gouezel's bounded variation code.
If `sl sr` are two subsets of `s`, `sl` to the left of `sr` the sum of the restricted lengths
is less or equal than the length.
-/
-- Probably deserves specializations for intervals
lemma path_length_ge_parts (l r : set β) (lr : ∀ x ∈ l, ∀ y ∈ r, x ≤ y) :
  (f ∘ (coe : subtype l → β)).path_length + (f ∘ (coe : subtype r → β)).path_length ≤ (f.path_length) :=
begin
  apply ennreal.bsupr_add_bsupr_le sorted_list_nonempty sorted_list_nonempty,
  rintro left lefts right rights,
  simp_rw [←length_on_map f coe],
  apply (f.length_on_append _ _).trans,
  dsimp [path_length],
  refine @le_supr₂ _ _ _ _ (λ l H, f.length_on l) _ _,
  rw list.pairwise_append,
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
                + (f ∘ (coe : {x // x ≥ m} → β)).path_length :=
begin
  dsimp [path_length],
  apply le_antisymm,
  { rw supr₂_le_iff,
    rintro l ls,
    let left := list.take_while (≤m) l,
    let right := list.drop_while (≤m) l,
    rw ←list.take_while_append_drop (≤m) l,
    apply (length_on_le_append_singleton_append f _ m _).trans,
    rw length_on_append_singleton_append,
    refine add_le_add _ _,
    { transitivity'
        (f ∘ coe).length_on (l.take_while_subtype m ++ [⟨m,le_refl m⟩]),
      { rw [←f.length_on_map coe, list.map_append, list.take_while_subtype_map_coe],
        simp only [list.map], simp only [subtype.coe_mk],
        finish, },
      { refine @le_supr₂ _ _ _ _ (λ l H, length_on (f ∘ coe) l) _ _,
        rw list.pairwise_append,
        dsimp [list.take_while_subtype], simp, sorry,  }

    },
    sorry,
    -- Need to change the lists `left,right` to live in the correct sets
  },
  { apply path_length_ge_parts,
    rintro x xm y my, exact xm.trans my, },
end

/--
A path is rectifiable if any of its restriction to a close interval has finite length
-/
def is_rectifiable :=
  ∀ (a b : β), (f ∘ (λ x : Icc a b, x.val)).path_length ≠ ⊤

def arc_length (x₀ : ℝ) : ℝ → ℝ :=
λ x,
  if h : x₀ ≤ x then
    (f ∘ inclusion (set.inter_subset_left s (Icc x₀ x))).path_length.to_real
  else
    - (f ∘ inclusion (set.inter_subset_left s (Icc x x₀))).path_length.to_real

lemma arc_length_monotone (hs : f.is_rectifiable)
  (x₀ : ℝ) (x₀s : x₀ ∈ s) : monotone (f.arc_length x₀) :=
begin
  rintro x₁ x₂ h,
  dsimp [arc_length],
  split_ifs with h₁ h₂ h₂ h₁,
  { transitivity'
      (path_length (f ∘ inclusion (set.inter_subset_left s (Icc x₀ x₁)))).to_real +
      (path_length (f ∘ inclusion (set.inter_subset_left s (Icc x₁ x₂)))).to_real,
    simp only [le_add_iff_nonneg_right, ennreal.to_real_nonneg],
    rw ←ennreal.to_real_add, rotate, apply hs, apply hs,
    refine ennreal.to_real_mono _ _, apply hs,
    apply path_length_ge_parts, -- Should use specialized version of `path_length_ge_parts`
    { rintro x ⟨xs,⟨x₀x,xx₁⟩⟩, exact ⟨xs,x₀x,xx₁.trans h⟩ },
    { rintro x ⟨xs,⟨x₁x,xx₂⟩⟩, exact ⟨xs,h₁.trans x₁x,xx₂⟩},
    { rintro x ⟨xs,x₀x,xx₁⟩ y ⟨ys,x₁y,yx₂⟩, exact xx₁.trans x₁y, }, },
  { exfalso, apply h₂ (h₁.trans h), },
  { transitivity' 0;
    simp only [right.neg_nonpos_iff, ennreal.to_real_nonneg];
    apply ennreal.to_real_nonneg, },
  -- this whole block ↓ is taken from the first. Intelligent tactic management should help ged rid of it
  { simp only [neg_le_neg_iff, not_le] at h₁ h₂ ⊢,
    transitivity'
      (path_length (f ∘ inclusion (set.inter_subset_left s (Icc x₁ x₂)))).to_real +
      (path_length (f ∘ inclusion (set.inter_subset_left s (Icc x₂ x₀)))).to_real,
    simp only [le_add_iff_nonneg_left, ennreal.to_real_nonneg],
    rw ←ennreal.to_real_add, rotate, apply hs, apply hs,
    refine ennreal.to_real_mono _ _, apply hs,
    apply path_length_ge_parts,
    { rintro x ⟨xs,⟨x₁x,xx₂⟩⟩, exact ⟨xs,x₁x,xx₂.trans h₂.le⟩ },
    { rintro x ⟨xs,⟨x₂x,xx₀⟩⟩, exact ⟨xs,h.trans x₂x, xx₀⟩},
    { rintro x ⟨xs,x₀x,xx₁⟩ y ⟨ys,x₁y,yx₂⟩, exact xx₁.trans x₁y, }, }
end

-- TODO: constant speed reparameterization

end path_length

section curve_length

variables {α : Type*} [metric_space α]

-- Say a curve has domain an Icc

end curve_length

end function
