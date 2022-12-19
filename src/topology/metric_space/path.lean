import data.real.ennreal
import data.real.nnreal
import data.set.intervals.basic
import topology.metric_space.emetric_space
import topology.metric_space.basic
import data.list.destutter
import topology.metric_space.lipschitz
import topology.instances.ennreal
import data.sign

noncomputable theory

open_locale classical ennreal

open emetric nnreal set

-- TODO: allow `[emetric_space α]`
-- Add Lipschitz maps

section preliminaries



end preliminaries

namespace function

section length_on

variables {α β : Type*} [metric_space α]
variables (f : β → α)

@[simp] def dist_head : β → list β → nnreal
| _ [] := 0
| x (a :: _) := nndist (f x) (f a)

@[simp] lemma dist_head_nil (b : β) : f.dist_head b [] = 0 := rfl
@[simp] lemma dist_head_cons (b) (a) (l) : f.dist_head b (a::l) = nndist (f b) (f a) := rfl

@[simp] lemma dist_head_le_append (b) (l l') : f.dist_head b l ≤ f.dist_head b (l ++ l') := sorry

lemma dist_head_triangle (a b) (l) :
  f.dist_head a l ≤ nndist (f a) (f b) + f.dist_head b l :=
begin
  induction l,
  simp only [dist_head_nil, zero_le'],
  simp only [dist_head_cons], apply nndist_triangle,
end

@[simp] def dist_tail_head : list β → list β → nnreal
| [] _ := 0
| [a] l' := f.dist_head a l'
| (a::l) l' := dist_tail_head l l'

def length_on : list β → nnreal
| list.nil := 0
| (a :: l) := f.dist_head a l + length_on l

@[simp] lemma length_on_nil : f.length_on list.nil = 0 := rfl
@[simp] lemma length_on_cons_nil (b : β) : f.length_on [b] = 0 :=
by simp only [length_on, dist_head_nil, add_zero]
@[simp] lemma length_on_cons_cons (a b : β) (l : list β) :
  f.length_on (a :: b :: l) = nndist (f a) (f b) + f.length_on (b :: l) := rfl

lemma length_on_cons_eq_dist_head_add_length_on (a : β) (l : list β) :
  f.length_on (a :: l) = f.dist_head a l + f.length_on l := rfl

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
  { simp only [length_on_cons_cons], rw ←add_assoc, apply add_le_add_right, apply le_add_left, refl, }

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
  ∀ l, f.length_on l = f.length_on (list.destutter (≠) l) := sorry

lemma length_on_append : ∀ l l', f.length_on l + f.length_on l' ≤ f.length_on (l ++ l')
| [] l' := by
  { simp only [list.nil_append, length_on_nil, zero_add], }
| [a] l' := by
  { simp only [list.singleton_append, length_on_cons_nil, zero_add],
    apply length_on_le_length_on_cons, }
| (a :: b :: l) l' := by
  { simp only [list.cons_append, length_on_cons_cons, add_assoc],
    apply add_le_add_left,
    apply length_on_append, }

lemma length_on_le_length_on_append_left
  (l l' : list β) : f.length_on l ≤ f.length_on (l ++ l') :=
le_trans (by { simp only [le_add_iff_nonneg_right, zero_le'], }) (f.length_on_append l l')

lemma length_on_le_length_on_append_right
  (l l' : list β) : f.length_on l' ≤ f.length_on (l ++ l') :=
le_trans (by { simp only [le_add_iff_nonneg_left, zero_le'], }) (f.length_on_append l l')

lemma length_on_reverse : ∀ (l : list β), f.length_on l.reverse = f.length_on l
| [] := rfl
| [a] := rfl
| (a :: b :: l) := by
  { simp only [list.reverse_cons, list.append_assoc, list.singleton_append,
               length_on_append_cons_cons, length_on_cons_cons],
    rw [←list.reverse_cons, length_on_reverse, add_comm, nndist_comm], }

@[simp]
lemma length_on_map {γ : Type*} (φ : γ → β) :
  ∀ (l : list γ), f.length_on (l.map φ) = (f ∘ φ).length_on l
| [] := by { simp only [list.map_nil, length_on_nil], }
| [a] := by { simp only [list.map, length_on_cons_nil], }
| (a :: b :: l)  := by
  { simp only [list.map, length_on_cons_cons, add_right_inj],
    rw ←list.map, apply length_on_map, }

lemma length_on_le_append_singleton_append :
  ∀ (l) (x) (l'), f.length_on (l ++ l') ≤ f.length_on (l ++ [x] ++ l')
| [] x l' := by { simp only [list.nil_append, list.singleton_append, length_on_le_length_on_cons], }
| [a] x l' := by
  { simp only [list.singleton_append, list.cons_append, length_on_cons_cons],
    simp only [list.nil_append, list.singleton_append, length_on_drop_second_cons_le], }
| (a :: b :: l) x l' := by
  { sorry, }


lemma length_on_append_singleton_append :
  ∀ (l) (x) (l'), f.length_on (l ++ [x] ++ l') = f.length_on (l ++ [x]) + f.length_on ([x] ++ l')
| [] x l' := by { simp only [list.nil_append, length_on_cons_nil, zero_add], }
| [a] x l' := by
  { simp only [list.singleton_append, list.cons_append, length_on_cons_cons,
               length_on_cons_nil, add_zero, add_left_inj, eq_self_iff_true], simp, }
| (a :: b :: l) x l' := by
  { simp only [list.cons_append, list.append_assoc, list.singleton_append, length_on_cons_cons],
    have : b :: (l ++ x :: l') = (b :: l) ++ [x] ++ l', by simp,
    rw [this, length_on_append_singleton_append, add_assoc], refl,  }

lemma length_on_mono' :
  ∀ l l', l <+ l' → (∀ x, f.dist_head x l + f.length_on l ≤ f.dist_head x l' + f.length_on l') :=
begin
  rintro l l' ll',
  induction ll' with l l' b ll' ih l l' b ll' ih,
  { simp only [dist_head_nil, length_on_nil, add_zero, le_zero_iff, eq_self_iff_true,
               implies_true_iff], },
  { rintro x,
    apply (ih x).trans,
    simp_rw [length_on_cons_eq_dist_head_add_length_on, dist_head_cons, ←add_assoc,
             add_le_add_iff_right],
    apply dist_head_triangle, },
  { rintro x, specialize ih b,
    simp [length_on_cons_eq_dist_head_add_length_on], exact ih, }
end

lemma length_on_mono : ∀ l l', l <+ l' → f.length_on l ≤ f.length_on l' :=
begin
  rintro l l' ll',
  cases l',
  { simp only [length_on_nil, le_zero_iff, list.sublist_nil_iff_eq_nil] at ll' ⊢,
    cases ll',
    refl, },
  { let := f.length_on_mono' _ _ ll' l'_hd,
    simp only [dist_head_cons, nndist_self, zero_add] at this,
    apply le_trans _ this, simp only [le_add_iff_nonneg_left, zero_le'],  }
end



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

def sorted_list_nonempty : set.nonempty {l : list s | l.pairwise (≤)} := ⟨[],list.pairwise.nil⟩

lemma path_length_comp_mono (φ : t → s) (mφ : monotone φ) :
  (f ∘ φ).path_length ≤ f.path_length :=
begin
  simp only [path_length, supr₂_le_iff, ←f.length_on_map φ],
  rintro l ls,
  exact @le_supr₂ _ _ _ _
    (λ (l : list ↥s) (H : list.pairwise (≤) l), (↑(f.length_on l) : ennreal))
    (l.map φ) (list.pairwise.map φ mφ ls),
end

lemma path_length_comp_anti (φ : t → s) (mφ : antitone φ) :
  (f ∘ φ).path_length ≤ f.path_length :=
begin
  simp only [path_length, supr₂_le_iff, ←f.length_on_map φ],
  rintro l ls,
  rw [←f.length_on_reverse, ←list.map_reverse],
  refine @le_supr₂ _ _ _ _
    (λ (l : list ↥s) (H : list.pairwise (≤) l), (↑(f.length_on l) : ennreal))
    _ _,
  apply list.pairwise.map φ _ (list.pairwise_reverse.mpr ls),
  rintro a b h, exact mφ h,
end


lemma path_length_mono (h : t ⊆ s) : (f ∘ inclusion h).path_length ≤ f.path_length :=
begin
  apply path_length_comp_mono,
  rintro ⟨a,ha⟩ ⟨b,hb⟩,
  exact id,
end

lemma path_length_reparametrize_mono (φ : t → s) (mφ : monotone φ) (sφ : surjective φ) :
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

lemma path_length_reparametrize_anti (φ : t → s) (mφ : antitone φ) (sφ : surjective φ) :
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


lemma _root_.ennreal.add_le_add {a b c d : ℝ≥0∞} (ac : a ≤ c) (bd : b ≤ d) : a + b ≤ c + d :=
by {transitivity' a + d, exact add_le_add_left bd a, exact add_le_add_right ac d }

/-- Statement ~copied from Gouezel's bounded variation code.
If `sl sr` are two subsets of `s`, `sl` to the left of `sr` the sum of the restricted lengths
is less or equal than the length.
-/
-- Probably deserves specializations for intervals
lemma path_length_ge_parts (sl sr : set ℝ) (sls : sl ⊆ s) (srs : sr ⊆ s)
  (lr : ∀ x ∈ sl, ∀ y ∈ sr, x ≤ y) :
  (f ∘ (inclusion sls)).path_length + (f ∘ (inclusion srs)).path_length ≤ (f.path_length) :=
begin
  apply ennreal.bsupr_add_bsupr_le sorted_list_nonempty sorted_list_nonempty,
  rintro left lefts right rights,
  simp_rw [←length_on_map f (inclusion _), ←ennreal.coe_add],
  apply (ennreal.coe_mono (f.length_on_append _ _)).trans,
  refine @le_supr₂ _ _ _ _
    (λ (l : list ↥s) (H : list.pairwise (≤) l), (↑(f.length_on l) : ennreal))
    _ _,
  rw list.pairwise_append,
  refine ⟨list.pairwise.map _ (λ a b h, h) lefts,
          list.pairwise.map _ (λ a b h, h) rights,
          λ x xleft y yright, _⟩,
  simp only [list.mem_map, set_coe.exists, inclusion_mk] at xleft yright,
  obtain ⟨a,bl,_,rfl⟩ := xleft,
  obtain ⟨b,ar,_,rfl⟩ := yright,
  exact lr a bl b ar,
end

-- Probably deserves specializations for intervals
lemma path_length_glue_split (sl sr : set ℝ) (sls : sl ⊆ s) (srs : sr ⊆ s)
  (lr : ∀ x ∈ sl, ∀ y ∈ sr, x ≤ y) (m : ℝ) (ms : m ∈ s)
  (cap : sl ∩ sr = {m}) (cup : sl ∪ sr = s) :
  f.path_length = (f ∘ (inclusion sls)).path_length + (f ∘ (inclusion srs)).path_length :=
begin
  subst_vars,
  have : ∀ x, x ∈ sl ∪ sr → x ≤ m → x ∈ sl := λ x xcup xm, by
  { cases xcup, exact xcup,
    have : m ∈ sl := (inter_subset_left sl sr) (cap.symm ▸ mem_singleton m),
    specialize lr m ‹m∈sl› x xcup,
    exact (le_antisymm xm lr).symm ▸ ‹m∈sl›, },
  dsimp [path_length],
  apply le_antisymm,
  { rw supr₂_le_iff,
    rintro l ls,
    let left := list.take_while (λ a, ↑a<m) l,
    let right := list.drop_while (λ a, ↑a<m) l,
    rw ←list.take_while_append_drop (λ a, ↑a < m ) l,
    apply (ennreal.coe_mono (length_on_le_append_singleton_append f _ ⟨m,ms⟩ _)).trans,
    rw length_on_append_singleton_append,
    simp only [list.singleton_append, ennreal.coe_add],
    apply _root_.ennreal.add_le_add,
    sorry,
    sorry,
    -- Need to change the lists `left,right` to live in the correct sets
  },
  { apply path_length_ge_parts,
    exact lr, },
end

/--
A path is rectifiable if any of its restriction to a close interval has finite length
-/
def is_rectifiable :=
  ∀ (a b : ℝ), (f ∘ inclusion (set.inter_subset_left s (Icc a b))).path_length ≠ ⊤

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
  split_ifs,
  { transitivity'
      (path_length (f ∘ inclusion (set.inter_subset_left s (Icc x₀ x₁)))).to_real +
      (path_length (f ∘ inclusion (set.inter_subset_left s (Icc x₁ x₂)))).to_real,
    simp only [le_add_iff_nonneg_right, ennreal.to_real_nonneg],
    rw ←ennreal.to_real_add, rotate, apply hs, apply hs,
    refine ennreal.to_real_mono _ _, apply hs,
    apply path_length_ge_parts, -- Should use specialized version of `path_length_ge_parts`
    { rintro x ⟨xs,⟨x₀x,xx₁⟩⟩, exact ⟨xs,x₀x,xx₁.trans h⟩ },
    { rintro x ⟨xs,⟨x₁x,xx₂⟩⟩, exact ⟨xs,h_1.trans x₁x,xx₂⟩},
    { rintro x ⟨xs,x₀x,xx₁⟩ y ⟨ys,x₁y,yx₂⟩, exact xx₁.trans x₁y, }, },
  { exfalso, apply h_2 (h_1.trans h), },
  { transitivity' 0;
    simp only [right.neg_nonpos_iff, ennreal.to_real_nonneg];
    apply ennreal.to_real_nonneg, },
  -- this whole block ↓ is taken from the first. Intelligent tactic management should help ged rid of it
  { simp only [neg_le_neg_iff, not_le] at h_1 h_2 ⊢,
    transitivity'
      (path_length (f ∘ inclusion (set.inter_subset_left s (Icc x₁ x₂)))).to_real +
      (path_length (f ∘ inclusion (set.inter_subset_left s (Icc x₂ x₀)))).to_real,
    simp only [le_add_iff_nonneg_left, ennreal.to_real_nonneg],
    rw ←ennreal.to_real_add, rotate, apply hs, apply hs,
    refine ennreal.to_real_mono _ _, apply hs,
    apply path_length_ge_parts,
    { rintro x ⟨xs,⟨x₁x,xx₂⟩⟩, exact ⟨xs,x₁x,xx₂.trans h_2.le⟩ },
    { rintro x ⟨xs,⟨x₂x,xx₀⟩⟩, exact ⟨xs,h.trans x₂x, xx₀⟩},
    { rintro x ⟨xs,x₀x,xx₁⟩ y ⟨ys,x₁y,yx₂⟩, exact xx₁.trans x₁y, },
   }
end

end path_length

section curve_length

variables {α : Type*} [metric_space α]

-- Say a curve has domain an Icc

end curve_length

end function
