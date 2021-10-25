/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import topology.opens
import ring_theory.ideal.prod
import linear_algebra.finsupp
import algebra.punit_instances
import ring_theory.homogeneous_ideal
import algebra.direct_sum.ring
/-!
# Prime spectrum of a commutative ring

The prime spectrum of a commutative ring is the type of all prime ideals.
It is naturally endowed with a topology: the Zariski topology.

(It is also naturally endowed with a sheaf of rings,
which is constructed in `algebraic_geometry.structure_sheaf`.)

## Main definitions

* `prime_spectrum R`: The prime spectrum of a commutative ring `R`,
  i.e., the set of all prime ideals of `R`.
* `zero_locus s`: The zero locus of a subset `s` of `R`
  is the subset of `prime_spectrum R` consisting of all prime ideals that contain `s`.
* `vanishing_ideal t`: The vanishing ideal of a subset `t` of `prime_spectrum R`
  is the intersection of points in `t` (viewed as prime ideals).

## Conventions

We denote subsets of rings with `s`, `s'`, etc...
whereas we denote subsets of prime spectra with `t`, `t'`, etc...

## Inspiration/contributors

The contents of this file draw inspiration from
<https://github.com/ramonfmir/lean-scheme>
which has contributions from Ramon Fernandez Mir, Kevin Buzzard, Kenny Lau,
and Chris Hughes (on an earlier repository).

-/

noncomputable theory
open_locale classical direct_sum big_operators pointwise
open direct_sum

variables {ι : Type*} [linear_ordered_cancel_add_comm_monoid ι]
variables (A : ι → Type*) [Π i, add_comm_group (A i)] [gcomm_semiring A]
/-- `irrelavent_ideal` is the ideal generated by homogeneous element of positie grading-/
def irrelavent_ideal : ideal (⨁ i, A i) :=
  ideal.span (graded_monoid.to_direct_sum '' { x | 0 < x.1})

lemma homogeneous_irrelavent_ideal : homogeneous_ideal (irrelavent_ideal A) :=
⟨{x | 0 < x.1}, rfl⟩

/-- The prime spectrum of a commutative ring `R`
is the type of all prime ideals of `R`.

It is naturally endowed with a topology (the Zariski topology),
and a sheaf of commutative rings (see `algebraic_geometry.structure_sheaf`).
It is a fundamental building block in algebraic geometry. -/

def prime_spectrum_of_graded_ring :=
  {I : ideal (⨁ i, A i) //
    I.is_prime ∧ homogeneous_ideal I ∧ ¬(irrelavent_ideal A ≤ I)}

namespace prime_spectrum_of_graded_ring

variable {A}

/-- A method to view a point in the prime spectrum of a commutative ring
as an ideal of that ring. -/
abbreviation as_ideal (x : prime_spectrum_of_graded_ring A) : ideal (⨁ i, A i) := x.val

instance is_prime (x : prime_spectrum_of_graded_ring A) :
  x.as_ideal.is_prime := x.2.1

/--
The prime spectrum of the zero ring is empty.
-/
lemma punit (x : prime_spectrum_of_graded_ring (λ _ : ι, punit)) : false :=
begin
  apply x.1.ne_top_iff_one.1 x.2.1.1,
  convert x.1.zero_mem, ext j,
end

section
-- product of graded ring goes to here
end

@[ext] lemma ext {x y : prime_spectrum_of_graded_ring A} :
  x = y ↔ x.as_ideal = y.as_ideal :=
subtype.ext_iff_val

/-- The zero locus of a set `s` of elements of a commutative ring `R`
is the set of all prime ideals of the ring that contain the set `s`.

An element `f` of `R` can be thought of as a dependent function
on the prime spectrum of `R`.
At a point `x` (a prime ideal)
the function (i.e., element) `f` takes values in the quotient ring `R` modulo the prime ideal `x`.
In this manner, `zero_locus s` is exactly the subset of `prime_spectrum R`
where all "functions" in `s` vanish simultaneously.
-/

def zero_locus (s : set (⨁ i, A i)) : set (prime_spectrum_of_graded_ring A) :=
{x | s ⊆ x.as_ideal}

@[simp] lemma mem_zero_locus (x : prime_spectrum_of_graded_ring A) (s : set (⨁ i, A i)) :
  x ∈ zero_locus s ↔ s ⊆ x.as_ideal := iff.rfl

@[simp] lemma zero_locus_span (s : set (⨁ i, A i)) :
  zero_locus (ideal.span s : set (⨁ i, A i)) = zero_locus s :=
by { ext x, exact (submodule.gi _ _).gc s x.as_ideal }

/-- The vanishing ideal of a set `t` of points
of the prime spectrum of a commutative ring `R`
is the intersection of all the prime ideals in the set `t`.

An element `f` of `R` can be thought of as a dependent function
on the prime spectrum of `R`.
At a point `x` (a prime ideal)
the function (i.e., element) `f` takes values in the quotient ring `R` modulo the prime ideal `x`.
In this manner, `vanishing_ideal t` is exactly the ideal of `R`
consisting of all "functions" that vanish on all of `t`.
-/
def vanishing_ideal (t : set (prime_spectrum_of_graded_ring A)) : ideal (⨁ i, A i) :=
⨅ (x : prime_spectrum_of_graded_ring A) (h : x ∈ t), x.as_ideal

lemma coe_vanishing_ideal (t : set (prime_spectrum_of_graded_ring A)) :
  (vanishing_ideal t : set (⨁ i, A i)) =
  {f : ⨁ i, A i | ∀ x : prime_spectrum_of_graded_ring A, x ∈ t → f ∈ x.as_ideal} :=
begin
  ext f,
  rw [vanishing_ideal, set_like.mem_coe, submodule.mem_infi],
  apply forall_congr, intro x,
  rw [submodule.mem_infi],
end

lemma mem_vanishing_ideal (t : set (prime_spectrum_of_graded_ring A)) (f : ⨁ i, A i) :
  f ∈ vanishing_ideal t ↔ ∀ x : prime_spectrum_of_graded_ring A, x ∈ t → f ∈ x.as_ideal :=
by rw [← set_like.mem_coe, coe_vanishing_ideal, set.mem_set_of_eq]

@[simp] lemma vanishing_ideal_singleton (x : prime_spectrum_of_graded_ring A) :
  vanishing_ideal ({x} : set (prime_spectrum_of_graded_ring A)) = x.as_ideal :=
by simp [vanishing_ideal]

lemma subset_zero_locus_iff_le_vanishing_ideal (t : set (prime_spectrum_of_graded_ring A))
  (I : ideal (⨁ i, A i)) :
  t ⊆ zero_locus I ↔ I ≤ vanishing_ideal t :=
⟨λ h f k, (mem_vanishing_ideal _ _).mpr (λ x j, (mem_zero_locus _ _).mpr (h j) k), λ h,
  λ x j, (mem_zero_locus _ _).mpr (le_trans h (λ f h, ((mem_vanishing_ideal _ _).mp h) x j))⟩

section gc
variable (A)

/-- `zero_locus` and `vanishing_ideal` form a galois connection. -/
lemma gc : @galois_connection
  (ideal (⨁ i, A i)) (order_dual (set (prime_spectrum_of_graded_ring A))) _ _
  (λ I, zero_locus I) (λ t, vanishing_ideal t) :=
λ I t, subset_zero_locus_iff_le_vanishing_ideal t I

/-- `zero_locus` and `vanishing_ideal` form a galois connection. -/
lemma gc_set : @galois_connection
  (set (⨁ i, A i)) (order_dual (set (prime_spectrum_of_graded_ring A))) _ _
  (λ s, zero_locus s) (λ t, vanishing_ideal t) :=
have ideal_gc : galois_connection (ideal.span) coe := (submodule.gi (⨁ i, A i) _).gc,
by simpa [zero_locus_span, function.comp] using galois_connection.compose _ _ _ _ ideal_gc (gc _)

lemma subset_zero_locus_iff_subset_vanishing_ideal (t : set (prime_spectrum_of_graded_ring A))
  (s : set (⨁ i, A i)) :
  t ⊆ zero_locus s ↔ s ⊆ vanishing_ideal t :=
(gc_set _) s t

end gc

lemma subset_vanishing_ideal_zero_locus (s : set (⨁ i, A i)) :
  s ⊆ vanishing_ideal (zero_locus s) :=
(gc_set _).le_u_l s

lemma le_vanishing_ideal_zero_locus (I : ideal (⨁ i, A i)) :
  I ≤ vanishing_ideal (zero_locus I) :=
(gc _).le_u_l I

-- @[simp] lemma vanishing_ideal_zero_locus_eq_radical (I : ideal R) :
--   vanishing_ideal (zero_locus (I : set R)) = I.radical := ideal.ext $ λ f,
-- begin
--   rw [mem_vanishing_ideal, ideal.radical_eq_Inf, submodule.mem_Inf],
--   exact ⟨(λ h x hx, h ⟨x, hx.2⟩ hx.1), (λ h x hx, h x.1 ⟨hx, x.2⟩)⟩
-- end

-- @[simp] lemma zero_locus_radical (I : ideal R) : zero_locus (I.radical : set R) = zero_locus I :=
-- vanishing_ideal_zero_locus_eq_radical I ▸ congr_fun (gc R).l_u_l_eq_l I

-- lemma subset_zero_locus_vanishing_ideal (t : set (prime_spectrum R)) :
--   t ⊆ zero_locus (vanishing_ideal t) :=
-- (gc R).l_u_le t

-- lemma zero_locus_anti_mono {s t : set R} (h : s ⊆ t) : zero_locus t ⊆ zero_locus s :=
-- (gc_set R).monotone_l h

-- lemma zero_locus_anti_mono_ideal {s t : ideal R} (h : s ≤ t) :
--   zero_locus (t : set R) ⊆ zero_locus (s : set R) :=
-- (gc R).monotone_l h

-- lemma vanishing_ideal_anti_mono {s t : set (prime_spectrum R)} (h : s ⊆ t) :
--   vanishing_ideal t ≤ vanishing_ideal s :=
-- (gc R).monotone_u h

-- lemma zero_locus_subset_zero_locus_iff (I J : ideal R) :
--   zero_locus (I : set R) ⊆ zero_locus (J : set R) ↔ J ≤ I.radical :=
-- ⟨λ h, ideal.radical_le_radical_iff.mp (vanishing_ideal_zero_locus_eq_radical I ▸
--   vanishing_ideal_zero_locus_eq_radical J ▸ vanishing_ideal_anti_mono h),
-- λ h, zero_locus_radical I ▸ zero_locus_anti_mono_ideal h⟩

-- lemma zero_locus_subset_zero_locus_singleton_iff (f g : R) :
--   zero_locus ({f} : set R) ⊆ zero_locus {g} ↔ g ∈ (ideal.span ({f} : set R)).radical :=
-- by rw [← zero_locus_span {f}, ← zero_locus_span {g}, zero_locus_subset_zero_locus_iff,
--     ideal.span_le, set.singleton_subset_iff, set_like.mem_coe]

lemma zero_locus_bot :
  zero_locus ((⊥ : ideal (⨁ i, A i)) : set (⨁ i, A i)) = set.univ :=
(gc A).l_bot

@[simp] lemma zero_locus_singleton_zero :
  zero_locus ({0} : set (⨁ i, A i)) = set.univ :=
zero_locus_bot

@[simp] lemma zero_locus_empty :
  zero_locus (∅ : set (⨁ i, A i)) = set.univ :=
(gc_set A).l_bot

@[simp] lemma vanishing_ideal_univ :
  vanishing_ideal (∅ : set (prime_spectrum_of_graded_ring A)) = ⊤ :=
by simpa using (gc A).u_top

lemma zero_locus_empty_of_one_mem {s : set (⨁ i, A i)} (h : (1:(⨁ i, A i)) ∈ s) :
  zero_locus s = ∅ :=
begin
  rw set.eq_empty_iff_forall_not_mem,
  intros x hx,
  rw mem_zero_locus at hx,
  have x_prime : x.as_ideal.is_prime := by apply_instance,
  have eq_top : x.as_ideal = ⊤, { rw ideal.eq_top_iff_one, exact hx h },
  apply x_prime.ne_top eq_top,
end

@[simp] lemma zero_locus_singleton_one :
  zero_locus ({1} : set (⨁ i, A i)) = ∅ :=
zero_locus_empty_of_one_mem (set.mem_singleton (1 : ⨁ i, A i))

-- lemma zero_locus_empty_iff_eq_top {I : ideal (⨁ i, A i)} :
--   zero_locus (I : set (⨁ i, A i)) = ∅ ↔ I = ⊤ :=
-- begin
--   split,
--   { contrapose!,
--     intro h,
--     apply set.ne_empty_iff_nonempty.mpr,
--     rcases ideal.exists_le_maximal I h with ⟨M, hM, hIM⟩,
--     exact ⟨⟨M, hM.is_prime⟩, hIM⟩ },
--   { rintro rfl, apply zero_locus_empty_of_one_mem, trivial }
-- end

@[simp] lemma zero_locus_univ :
  zero_locus (set.univ : set (⨁ i, A i)) = ∅ :=
zero_locus_empty_of_one_mem (set.mem_univ 1)

lemma zero_locus_sup (I J : ideal (⨁ i, A i)) :
  zero_locus ((I ⊔ J : ideal (⨁ i, A i)) : set (⨁ i, A i)) = zero_locus I ∩ zero_locus J :=
(gc A).l_sup

lemma zero_locus_union (s s' : set (⨁ i, A i)) :
  zero_locus (s ∪ s') = zero_locus s ∩ zero_locus s' :=
(gc_set A).l_sup

lemma vanishing_ideal_union (t t' : set (prime_spectrum_of_graded_ring A)) :
  vanishing_ideal (t ∪ t') = vanishing_ideal t ⊓ vanishing_ideal t' :=
(gc A).u_inf

lemma zero_locus_supr {γ : Sort*} (I : γ → ideal (⨁ i, A i)) :
  zero_locus ((⨆ i, I i : ideal (⨁ i, A i)) : set (⨁ i, A i)) = (⋂ i, zero_locus (I i)) :=
(gc A).l_supr

lemma zero_locus_Union {γ : Sort*} (s : γ → set (⨁ i, A i)) :
  zero_locus (⋃ i, s i) = (⋂ i, zero_locus (s i)) :=
(gc_set A).l_supr

lemma zero_locus_bUnion (s : set (set (⨁ i, A i))) :
  zero_locus (⋃ s' ∈ s, s' : set (⨁ i, A i)) = ⋂ s' ∈ s, zero_locus s' :=
by simp only [zero_locus_Union]

lemma vanishing_ideal_Union {γ : Sort*} (t : γ → set (prime_spectrum_of_graded_ring A)) :
  vanishing_ideal (⋃ i, t i) = (⨅ i, vanishing_ideal (t i)) :=
(gc A).u_infi

lemma zero_locus_inf (I J : ideal (⨁ i, A i)) :
  zero_locus ((I ⊓ J : ideal (⨁ i, A i)) : set (⨁ i, A i)) = zero_locus I ∪ zero_locus J :=
set.ext $ λ x, by simpa using x.2.1.inf_le

lemma union_zero_locus (s s' : set (⨁ i, A i)) :
  zero_locus s ∪ zero_locus s' = zero_locus ((ideal.span s) ⊓ (ideal.span s') : ideal (⨁ i, A i)) :=
by { rw zero_locus_inf, simp }

lemma zero_locus_mul (I J : ideal (⨁ i, A i)) :
  zero_locus ((I * J : ideal (⨁ i, A i)) : set (⨁ i, A i)) = zero_locus I ∪ zero_locus J :=
set.ext $ λ x, by simpa using x.2.1.mul_le

lemma zero_locus_singleton_mul (f g : (⨁ i, A i)) :
  zero_locus ({f * g} : set (⨁ i, A i)) = zero_locus {f} ∪ zero_locus {g} :=
set.ext $ λ x, by simpa using x.2.1.mul_mem_iff_mem_or_mem

-- @[simp] lemma zero_locus_pow (I : ideal (⨁ i, A i)) {n : ℕ} (hn : 0 < n) :
--   zero_locus ((I ^ n : ideal (⨁ i, A i)) : set (⨁ i, A i)) = zero_locus I :=
-- zero_locus_radical (I ^ n) ▸ (I.radical_pow n hn).symm ▸ zero_locus_radical I

@[simp] lemma zero_locus_singleton_pow (f : (⨁ i, A i)) (n : ℕ) (hn : 0 < n) :
  zero_locus ({f ^ n} : set (⨁ i, A i)) = zero_locus {f} :=
set.ext $ λ x, by simpa using x.2.1.pow_mem_iff_mem n hn

lemma sup_vanishing_ideal_le (t t' : set (prime_spectrum_of_graded_ring A)) :
  vanishing_ideal t ⊔ vanishing_ideal t' ≤ vanishing_ideal (t ∩ t') :=
begin
  intros r,
  rw [submodule.mem_sup, mem_vanishing_ideal],
  rintro ⟨f, hf, g, hg, rfl⟩ x ⟨hxt, hxt'⟩,
  rw mem_vanishing_ideal at hf hg,
  apply submodule.add_mem; solve_by_elim
end

lemma mem_compl_zero_locus_iff_not_mem {f : (⨁ i, A i)} {I : prime_spectrum_of_graded_ring A} :
  I ∈ (zero_locus {f} : set (prime_spectrum_of_graded_ring A))ᶜ ↔ f ∉ I.as_ideal :=
by rw [set.mem_compl_eq, mem_zero_locus, set.singleton_subset_iff]; refl

/-- The Zariski topology on the prime spectrum of a commutative ring
is defined via the closed sets of the topology:
they are exactly those sets that are the zero locus of a subset of the ring. -/
instance zariski_topology : topological_space (prime_spectrum_of_graded_ring A) :=
topological_space.of_closed (set.range prime_spectrum_of_graded_ring.zero_locus)
  (⟨set.univ, by simp⟩)
  begin
    intros Zs h,
    rw set.sInter_eq_Inter,
    let f : Zs → set _ := λ i, classical.some (h i.2),
    have hf : ∀ i : Zs, ↑i = zero_locus (f i) := λ i, (classical.some_spec (h i.2)).symm,
    simp only [hf],
    exact ⟨_, zero_locus_Union _⟩
  end
  (by { rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩, exact ⟨_, (union_zero_locus s t).symm⟩ })

lemma is_open_iff (U : set (prime_spectrum_of_graded_ring A)) :
  is_open U ↔ ∃ s, Uᶜ = zero_locus s :=
by simp only [@eq_comm _ Uᶜ]; refl

lemma is_closed_iff_zero_locus (Z : set (prime_spectrum_of_graded_ring A)) :
  is_closed Z ↔ ∃ s, Z = zero_locus s :=
by rw [← is_open_compl_iff, is_open_iff, compl_compl]

lemma is_closed_zero_locus (s : set (⨁ i, A i)) :
  is_closed (zero_locus s) :=
by { rw [is_closed_iff_zero_locus], exact ⟨s, rfl⟩ }

-- lemma zero_locus_vanishing_ideal_eq_closure (t : set (prime_spectrum_of_graded_ring A)) :
--   zero_locus (vanishing_ideal t : set (⨁ i, A i)) = closure t :=
-- begin
--   apply set.subset.antisymm,
--   { rintro x hx t' ⟨ht', ht⟩,
--     obtain ⟨fs, rfl⟩ : ∃ s, t' = zero_locus s,
--     by rwa [is_closed_iff_zero_locus] at ht',
--     rw [subset_zero_locus_iff_subset_vanishing_ideal] at ht,
--     exact set.subset.trans ht hx },
--   { rw (is_closed_zero_locus _).closure_subset_iff,
--     exact subset_zero_locus_vanishing_ideal t }
-- end

-- lemma vanishing_ideal_closure (t : set (prime_spectrum R)) :
--   vanishing_ideal (closure t) = vanishing_ideal t :=
-- zero_locus_vanishing_ideal_eq_closure t ▸ congr_fun (gc R).u_l_u_eq_u t


end prime_spectrum_of_graded_ring
