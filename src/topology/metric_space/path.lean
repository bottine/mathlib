import data.real.ennreal
import data.real.nnreal
import data.set.intervals.basic
import topology.metric_space.emetric_space
import topology.metric_space.basic

noncomputable theory

open_locale classical ennreal

open emetric nnreal set

-- TODO: allow `[emetric_space α]`
-- TODO: how to deal with paths defined non ICC intervals ?

section length_on

variables {α β : Type*} [metric_space α]
variables (f : β → α) (l l' : list β) (a b : β)

def function.length_on : nnreal :=
  list.sum (list.map₂ (λ x y, nndist (f x) (f y)) ([a] ++ l) (l ++ [b]))

@[simp]
lemma function.length_on_nil :
  f.length_on list.nil a b = nndist (f a) (f b) :=
begin
  dsimp [function.length_on],
  simp only [list.sum_cons, list.sum_nil, add_zero],
end

@[simp]
lemma function.length_on_cons (c : β):
  f.length_on (c :: l) a b = (nndist (f a) (f c)) + f.length_on l c b :=
begin
  dsimp [function.length_on],
  simp only [list.sum_cons],
end

lemma function.length_on_le_length_on_cons (c : β) :
  f.length_on l a b ≤ f.length_on (c :: l) a b :=
begin
  cases l,
  { dsimp [function.length_on],
    simp only [list.sum_cons, list.sum_nil, add_zero],
    apply nndist_triangle, },
  { simp_rw [function.length_on_cons, ←add_assoc], apply add_le_add_right, apply nndist_triangle },
end

lemma function.length_on_mono (ll' : l <+ l') :
  ∀ a b, f.length_on l a b ≤ f.length_on l' a b :=
begin
  induction ll' with l l' c ll' ih l l' c ll' ih,
  { rintro a b, simp only [le_refl], },
  { rintro a b, apply (ih a b).trans,
    apply function.length_on_le_length_on_cons, },
  { rintro a b,
    simp only [function.length_on_cons, add_le_add_iff_left],
    exact ih c b, }
end

lemma function.length_on_destutter :
  ∀ l a b, f.length_on l a b = f.length_on (list.destutter (≠) l) a b :=
begin
  sorry
end

end length_on

section path_length_on

variables {α : Type*} [metric_space α] {a b : nnreal} (ab : a ≤ b)
variables (f : Icc a b → α) (l : list $ Icc a b)

def function.path_length_on  : nnreal :=
  f.length_on l ⟨a, le_refl a, ab⟩ ⟨b, ab, le_refl b⟩

/--
The path length of `f` is the supremum over all strictly increasing partitions `l`
of the length of `f` for `l`
-/
def function.path_length : ennreal :=
  ⨆ l ∈ {l : list $ Icc a b | l.pairwise (≤)}, f.path_length_on ab l



end path_length_on



/-
section Path_Metric

parameters (α : Type*)

parameters (P : α → α → Type*)
           (Psymm : Π {a b : α}, P a b → P b a)
           (Ptran : Π {a b c : α}, P a b → P b c → P a c)

parameters (L : Π {a b : α}, P a b → ennreal)
           (Lrefl : Π a : α, infi (@L a a) = (0 : ennreal))
           (Lsymm : Π a b : α, Π p : P a b, L (Psymm p) ≤ L p)
           (Ltran : Π a b c : α, Π p : P a b, Π q : P b c, L (Ptran p q) ≤ L p + L q)

def edist (a b : α) : ennreal := infi (@L a b)

def edist_finite (a b : α) (p : P a b) (Hp : L p < ⊤) : edist a b < ⊤ := infi_lt_iff.mpr (⟨p, Hp⟩)
def edist_antisymm (a b : α) (ε : ennreal) (H : ε > 0) (Hab : Π p : P a b, L p ≥ ε) : edist a b ≥ ε := le_infi Hab
def edist_antisymm' (a b : α) (ε : ennreal) (H : ε > 0) (Hab : Π p : P a b, L p ≥ ε) : edist a b > 0 := gt_of_ge_of_gt (edist_antisymm a b ε H Hab) H



lemma edist_min (a b : α) (pmin : P a b) (Hmin : ∀ p : P a b, L pmin ≤ L p) : edist a b = L pmin :=
has_le.le.antisymm (infi_le (@L a b) pmin) (le_infi Hmin)

lemma edist_min_nat (a b : α)
  (hnat : ∀ p : P a b, ∃ np : ℕ, L p = np)
  (hnempty : nonempty (P a b)) :
∃ p : P a b, edist a b = L p :=
begin
  let Lℕ : set ℕ := {n : ℕ | ∃ (p : P a b), L p = n},
  have hLℕ : ∃ n, n ∈ Lℕ, by {
    let p := nonempty.some hnempty,
    rcases hnat p with ⟨np, pgood⟩,
    exact ⟨np,p,pgood⟩,},
  let n := nat.find hLℕ,
  rcases nat.find_spec hLℕ with ⟨p,pgood⟩,
  have : ∀ q : P a b, L p ≤ L q, by {
    intro q,
    rcases hnat q with ⟨nq,qgood⟩,
    have : nq ∈ Lℕ, from ⟨q,qgood⟩,
    have : n ≤ nq, from nat.find_min' hLℕ ‹nq∈Lℕ›,
    rw [qgood,pgood],
    exact coe_nat_le_coe_nat.mpr ‹n≤nq›,
  },
  use p,
  exact edist_min a b p this,
end

lemma edist_refl (a : α) : edist a a = 0 := Lrefl a

lemma edist_symm_le (a b : α) : edist a b ≤ edist b a :=
begin
  apply @infi_mono' _ _ _ _(@L a b) (@L b a),
  exact (Lsymm p)
end

lemma edist_symm (a b : α) : edist a b = edist b a :=
has_le.le.antisymm (edist_symm_le a b) (edist_symm_le b a)

lemma edist_triangle (a b c : α) : edist a c ≤ edist a b + edist b c :=
begin
  suffices : ∀ ε > 0, edist a c ≤ edist a b + edist b c + ε, by {
    sorry,
  },
  rintros ε hε,
  have p : P a b, by sorry,
  have hp : L p ≤ edist a b + ε/2, by sorry,
  have q : P b c, by sorry,
  have hq : L q ≤ edist b c + ε/2, by sorry,
  let pq := Ptran p q,
  have : L pq ≤ edist a b + edist b c + ε, by sorry,
  exact infi_le_of_le this,
end

end Path_Metric
-/
