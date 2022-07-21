import data.real.ennreal
import topology.metric_space.emetric_space

noncomputable theory

open_locale classical ennreal

open emetric ennreal




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
