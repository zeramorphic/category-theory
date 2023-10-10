import CategoryTheory.Basic

/-!
A collection of basic exercises from Johnstone's notes.
-/

namespace Category

variable {α β γ δ : Type _} {A B C D : α}
  [Category α] [Category β] [Category γ] [Category δ]

def imageCongruence (F : α ⥤ β) : Congruence α where
  rel A B f g := F.map f = F.map g
  equivalence := by intros; constructor <;> aesop
  rel_whisker := by intros; aesop
  whisker_rel := by intros; aesop

abbrev ImageQuotient (F : α ⥤ β) := HomQuotient (imageCongruence F)

def imageQuotientFunctor (F : α ⥤ β) : ImageQuotient F ⥤ β where
  obj A := F.obj A.unquot
  map f := Quotient.lift (fun f => F.map f) (fun _ _ h => by exact h) f
  map_id := F.map_id
  map_comp := by
    intro A B C f g
    refine Quotient.inductionOn₂ f g ?_
    exact F.map_comp

theorem imageQuotientFunctor_faithful (F : α ⥤ β) :
    Faithful (imageQuotientFunctor F) := by
  intro A B f g
  refine HomQuotient.inductionOn f ?_
  refine HomQuotient.inductionOn g ?_
  intro f g h
  rw [HomQuotient.quotHom_eq_iff]
  exact h

end Category
