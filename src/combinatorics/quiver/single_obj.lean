import combinatorics.quiver.symmetric

namespace quiver

def single_obj (α : Type*) : Type := unit

namespace single_obj

variables (α β γ : Type*)

instance : quiver (single_obj α) := ⟨λ _ _, α⟩

/-- The single object in `single_obj α`. -/
def star : single_obj α := unit.star

def has_reverse (rev : α → α) : has_reverse (single_obj α) := ⟨λ _ _, rev⟩
def has_involutive_reverse (rev : α → α) (h : function.involutive rev) :
  has_involutive_reverse (single_obj α) :=
{ to_has_reverse := has_reverse α rev,
  inv' := λ _ _, h}

variables {α β γ}

@[simps] def to_hom : α ≃ (star α ⟶ star α) := equiv.refl _

@[simps] def fun_equiv_prefunctor :
  (α → β) ≃ (single_obj α ⟶q single_obj β) :=
{ to_fun := λ f, ⟨id, λ _ _, f⟩,
  inv_fun := λ f a, f.map (to_hom a),
  left_inv := λ _, rfl,
  right_inv :=  λ f, by cases f; obviously }

@[simp] lemma fun_equiv_prefunctor_id : fun_equiv_prefunctor id = 𝟙q (single_obj α) := rfl
@[simp] lemma fun_equiv_prefunctor_symm_id :
  fun_equiv_prefunctor.symm (𝟙q (single_obj α)) = id := rfl
@[simp] lemma fun_equiv_prefunctor_comp (f : α → β) (g : β → γ) :
  fun_equiv_prefunctor (g ∘ f) = (fun_equiv_prefunctor f ≫q fun_equiv_prefunctor g) := rfl
@[simp] lemma fun_equiv_prefunctor_symm_comp (f : single_obj α ⟶q single_obj β)
  (g : single_obj β ⟶q single_obj γ) : fun_equiv_prefunctor.symm (f ≫q g) =
  (fun_equiv_prefunctor.symm g ∘ fun_equiv_prefunctor.symm f) :=
by simp only [equiv.symm_apply_eq, fun_equiv_prefunctor_comp, equiv.apply_symm_apply]

def path_to_list : Π {x : single_obj α}, path (star α) x → list α
| _ path.nil := []
| _ (path.cons p a) := a :: (path_to_list p)

@[simp] lemma path_to_list_nil : path_to_list path.nil = ([] : list α) := rfl
@[simp] lemma path_to_list_cons {x y : single_obj α} (p : path (star α) x) (a : x ⟶ y) :
  path_to_list (p.cons a) = a :: path_to_list p := rfl

def list_to_path : list α → path (star α) (star α)
| [] := path.nil
| (a :: l) := (list_to_path l).cons a

@[simp] lemma list_to_path_nil : list_to_path ([] : list α) = path.nil := rfl
@[simp] lemma list_to_path_cons (l : list α) (a : α) :
  list_to_path (a :: l) = (list_to_path l).cons a := rfl

lemma path_to_list_to_path {x : single_obj α} (p : path (star α) x) :
  list_to_path (path_to_list p) == p :=
by { induction p with y z p a ih, refl, tidy }

lemma list_to_path_to_list (l : list α) :
  path_to_list (list_to_path l) = l :=
by { induction l with a l ih, refl, simp [ih] }

@[simps] def path_equiv_list : path (star α) (star α) ≃ list α :=
⟨path_to_list, list_to_path, λ p, eq_of_heq (path_to_list_to_path p), list_to_path_to_list⟩

end single_obj

end quiver
