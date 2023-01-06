import measure_theory.measure.lebesgue
import analysis.calculus.monotone
import data.set.function
import analysis.bounded_variation

open_locale big_operators nnreal ennreal
open set measure_theory

variables {α β : Type*} [linear_order α] [linear_order β]
{E F : Type*} [pseudo_emetric_space E] [pseudo_emetric_space F]

lemma evariation_on.eq_zero_iff (f : α → E) {s : set α} :
  evariation_on f s = 0 ↔ ∀  (x y ∈ s), edist (f x) (f y) = 0 :=
begin
  split,
  { rintro h x xs y ys, rw [←le_zero_iff, ←h], apply evariation_on.edist_le f xs ys, },
  { rintro h, rw [←le_zero_iff], dsimp [evariation_on], apply supr_le _, rintro ⟨n,u,um,us⟩,
    apply finset.sum_nonpos _, rintro i hi, rw le_zero_iff, apply h _ (us i.succ) _ (us i), },
end

def is_linearly_parameterized_on_by (f : ℝ → E) (s : set ℝ) (l : ℝ) :=
∀ (x y ∈ s), evariation_on f (s ∩ Icc x y) = ennreal.of_real (l * (y - x))

def is_naturally_parameterized_on (f : ℝ → E) (s : set ℝ) :=
is_linearly_parameterized_on_by f s 1

lemma is_linearly_parameterized_on_by_zero_iff (f : ℝ → E) (s : set ℝ) :
  is_linearly_parameterized_on_by f s 0 ↔ ∀ x y ∈ s, edist (f x) (f y) = 0 :=
begin
  dsimp [is_linearly_parameterized_on_by],
  simp only [zero_mul, ennreal.of_real_zero, ←evariation_on.eq_zero_iff],
  sorry,
  -- One direction is by evariation being monotonous
  -- For the other, contrapositive: If evariation_on f s ≠ 0, there exists x y such that edist f x f y
  -- is not zero, which means that the evariation on s ∩ Icc x y won't be zero either.
  -- (we use `evariation_on.eq_zero_iff`) in both its directions
end

lemma test {f : ℝ → E} {s t : set ℝ} {φ : ℝ → ℝ}
  (φm : monotone_on φ s) (φst : s.maps_to φ t) (φst' : s.surj_on φ t) {l l' : ℝ}
  (hf : is_linearly_parameterized_on_by (f ∘ φ) s l) (hfφ : is_linearly_parameterized_on_by f t l')
  ⦃x : ℝ⦄ (xs : x ∈ s) : s.eq_on φ (λ y, (l / l') * (y - x) + (φ x)) :=
begin
  rintro y ys,
end
