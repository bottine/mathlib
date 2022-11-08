import combinatorics.quiver.basic

open function

universes u v w

namespace quiver

/- The class of quivers on `V` with arrows labelled by elements of `S` -/
class colored_quiver (V : Type*) (S : Type*) extends (quiver V) :=
(color : ∀ {x y}, (hom x y) → S)

def color {V S : Type*} [colored_quiver V S] {x y : V} (f : x ⟶ y) : S := colored_quiver.color f

structure colored_prefunctor (V V') {S S' : Type*} [colored_quiver V S] [colored_quiver V' S']
  (σ : S → S') extends V ⟶q V' :=
(color : ∀ {x y} (f : x ⟶ y), σ (color f) = color (map f))

notation V ` ⟶qc[ ` σ ` ] ` V' := colored_prefunctor V V' σ

def colored_prefunctor_comp {V V' V'' : Type*} {S S' S'' : Type*}
  [colored_quiver V S] [colored_quiver V' S'] [colored_quiver V'' S''] {σ : S → S'} {σ' : S' → S''}
  (F : V ⟶qc[ σ ] V') (F' : V' ⟶qc[ σ' ] V'') : V ⟶qc[ (σ' ∘ σ) ] V'' := sorry

end quiver
