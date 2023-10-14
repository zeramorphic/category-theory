import CategoryTheory.Basic

namespace Category

open Opposite

variable {α β γ δ : Type _} {A B C D : α}
  [Category α] [Category β] [Category γ] [Category δ]
  {F : α ⥤ Type _}

/-- The covariant hom functor. -/
def CoHom (A : α) : α ⥤ Type _ where
  obj B := A ⟶ B
  map f g := f ∘ g
  map_id := by aesop
  map_comp := by aesop

@[simp]
theorem coHom_obj : (CoHom A).obj B = (A ⟶ B) := rfl

@[simp]
theorem coHom_map : (CoHom A).map f = fun g => f ∘ g := rfl

/-- The covariant hom functor. -/
def ContraHom (A : α) : αᵒᵖ ⥤ Type _ where
  obj B := unop B ⟶ A
  map f g := g ∘ f
  map_id := by
    intro B
    funext f
    simp
    exact comp_id _
  map_comp := by
    intro B C D g f
    funext h
    simp
    rfl

def Φ (η : NatTrans (CoHom A) F) : F.obj A :=
  η.app A (𝟙 A)

def Ψ (x : F.obj A) : NatTrans (CoHom A) F where
  app B f := (F.map f) x
  naturality := by
    intro B C f
    funext g
    simp

@[simp]
theorem ΦΨ (x : F.obj A) : Φ (Ψ x) = x := by
  unfold Φ Ψ
  simp

@[simp]
theorem ΨΦ (η : NatTrans (CoHom A) F) : Ψ (Φ η) = η := by
  ext B
  funext f
  have := congrFun (η.naturality f) (𝟙 A)
  simp at this
  exact this.symm

/-- The Yoneda embedding of a category into its category of presheaves. -/
def Y (α : Type _) [Category α] : α ⥤ (αᵒᵖ ⥤ Type _) where
  obj A := CoHom (op A)
  map {A B} f := Ψ f
  map_id := by
    intro A
    refine NatTrans.ext _ _ ?_
    funext B f
    simp
    exact comp_id _
  map_comp := by
    intro A B C g f
    refine NatTrans.ext _ _ ?_
    funext D h
    unfold Ψ
    simp
    rfl

end Category
