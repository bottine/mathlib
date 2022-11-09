import combinatorics.quiver.basic

universes u v w

namespace quiver

namespace prefunctor

variables (U : Type*) [quiver.{u+1} U]
          (V : Type*) [quiver.{v+1} V]
          (W : Type*) [quiver.{w+1} W]

@[ext] structure iso extends prefunctor U V :=
(inv_prefunctor : prefunctor V U)
(left_inv : to_prefunctor ≫q inv_prefunctor = 𝟙q _)
(right_inv : inv_prefunctor ≫q to_prefunctor = 𝟙q _)



infix ` ≃q `:50 := iso

variables {U V W}


lemma iso.inv_unique (F : U ⟶q V) (G G' : V ⟶q U)
  (left_inv : F ≫q G = 𝟙q _) (right_inv : G ≫q F = 𝟙q _)
  (left_inv' : F ≫q G = 𝟙q _) (right_inv' : G ≫q F = 𝟙q _) : G = G' := sorry

lemma iso.to_prefunctor_ext (F G : U ≃q V) : F = G ↔ F.to_prefunctor = G.to_prefunctor :=
begin
  cases F, cases G,
  simp only [and_iff_left_iff_imp],
  rintro ⟨⟩, subst_vars,

  apply iso.inv_unique,
  exact F_left_inv,
  assumption, assumption, assumption,
end

def iso.id : U ≃q U :=
{ to_prefunctor := prefunctor.id U,
  inv_prefunctor := prefunctor.id U,
  left_inv := rfl,
  right_inv := rfl }

def iso.comp (F : U ≃q V) (G : V ≃q W) : U ≃q W :=
{ to_prefunctor := F.to_prefunctor ≫q G.to_prefunctor,
  inv_prefunctor := G.inv_prefunctor ≫q F.inv_prefunctor,
  left_inv := by
  { rw [prefunctor.comp_assoc, ←prefunctor.comp_assoc G.to_prefunctor],
    rw [G.left_inv], exact F.left_inv,  },
  right_inv := by
  { rw [prefunctor.comp_assoc, ←prefunctor.comp_assoc F.inv_prefunctor],
    rw [F.right_inv], exact G.right_inv,  }, }

def iso.symm (F : U ≃q V) : V ≃q U := ⟨F.inv_prefunctor, F.to_prefunctor, F.right_inv, F.left_inv⟩

lemma iso.comp_id {F : U ≃q V} : (iso.comp F $ iso.id) = F :=
begin
  dsimp [iso.comp, iso.id],
  rw iso.to_prefunctor_ext,
  dsimp [iso.to_prefunctor],
  simp only [prefunctor.comp_id],
end

lemma iso.id_comp {F : U ≃q V} : (iso.comp iso.id F) = F :=
begin
  dsimp [iso.comp, iso.id],
  rw iso.to_prefunctor_ext,
  dsimp [iso.to_prefunctor],
  simp only [prefunctor.id_comp],
end

end prefunctor

end quiver
