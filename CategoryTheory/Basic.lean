import CategoryTheory.Set

class Category.{v} (α : Type u) : Type (max u v) where
  Hom : α → α → Sort v
  id (A : α) : Hom A A
  comp {A B C : α} : Hom B C → Hom A B → Hom A C
  id_comp' {A B : α} (f : Hom A B) : comp (id B) f = f
  comp_id' {A B : α} (f : Hom A B) : comp f (id A) = f
  assoc' {A B C D : α} (h : Hom C D) (g : Hom B C) (f : Hom A B) :
    comp (comp h g) f = comp h (comp g f)

namespace Category

scoped infixr:10 " ⟶ " => Category.Hom
scoped infixr:90 " ∘ " => Category.comp
scoped notation "𝟙" => Category.id

variable {α β γ δ : Type _} {A B C D : α}
  [Category α] [Category β] [Category γ] [Category δ]

@[simp]
theorem comp_id (f : A ⟶ B) :
    f ∘ 𝟙 A = f :=
  comp_id' f

@[simp]
theorem id_comp (f : A ⟶ B) :
    𝟙 B ∘ f = f :=
  id_comp' f

@[simp]
theorem assoc (h : C ⟶ D) (g : B ⟶ C) (f : A ⟶ B) :
    (h ∘ g) ∘ f = h ∘ g ∘ f :=
  assoc' h g f

theorem whisker_eq (h : B ⟶ C) {f g : A ⟶ B} (w : f = g) :
    h ∘ f = h ∘ g :=
  by rw [w]

theorem eq_whisker {f g : B ⟶ C} (w : f = g) (h : A ⟶ B) :
    f ∘ h = g ∘ h :=
  by rw [w]

instance : Category (Type _) where
  Hom α β := α → β
  id _ := fun x => x
  comp f g := fun x => f (g x)
  id_comp' _ := rfl
  comp_id' _ := rfl
  assoc' _ _ _ := rfl

@[simp]
theorem Type.comp (g : β ⟶ γ) (f : α ⟶ β) :
    Category.comp g f = Function.comp g f :=
  rfl

structure Opposite (α : Sort u) :=
  unop : α

namespace Opposite

scoped notation:max α "ᵒᵖ" => Opposite α

def op (x : α) : αᵒᵖ := ⟨x⟩

instance [Category α] : Category αᵒᵖ where
  Hom α β := unop β ⟶ unop α
  id α := 𝟙 (unop α)
  comp f g := g ∘ f
  id_comp' f := comp_id f
  comp_id' f := id_comp f
  assoc' h g f := (assoc f g h).symm

end Opposite

open Opposite

@[ext]
structure Functor (α : Type u₁) (β : Type u₂) [Category.{v₁} α] [Category.{v₂} β] :
    Type (max u₁ u₂ v₁ v₂) where
  obj : α → β
  map {A B : α} : (A ⟶ B) → (obj A ⟶ obj B)
  map_id {A : α} : map (𝟙 A) = 𝟙 (obj A)
  map_comp {A B C : α} (g : B ⟶ C) (f : A ⟶ B) : map (g ∘ f) = map g ∘ map f

attribute [simp] Functor.map_id Functor.map_comp

scoped infixr:26 " ⥤ " => Functor

/-- The covariant powerset functor. -/
def Power : Type u ⥤ Type u where
  obj A := Set A
  map := Set.image
  map_id := by
    intro A
    funext S
    exact Set.image_id S
  map_comp := by
    intro A B C g f
    funext S
    exact Set.image_comp g f S

@[simp]
theorem Power_obj : Power.obj α = Set α := rfl

@[simp]
theorem Power_map : Power.map f = Set.image f := rfl

/-- The contravariant powerset functor. -/
def CoPower : (Type u)ᵒᵖ ⥤ Type u where
  obj A := Set (unop A)
  map := Set.preimage
  map_id := rfl
  map_comp _ _ := rfl

def Functor.id (α : Type _) [Category α] : α ⥤ α where
  obj A := A
  map f := f
  map_id := by simp
  map_comp := by simp

scoped notation "𝟭" => Functor.id

@[simp]
theorem Functor.id_obj : (𝟭 α).obj A = A := rfl

@[simp]
theorem Functor.id_map : (𝟭 α).map f = f := rfl

def Functor.comp (G : β ⥤ γ) (F : α ⥤ β) : α ⥤ γ where
  obj A := G.obj (F.obj A)
  map f := G.map (F.map f)
  map_id := by simp
  map_comp := by simp

scoped infixr:80 " ◌ " => Functor.comp

@[simp]
theorem Functor.comp_obj (G : β ⥤ γ) (F : α ⥤ β) :
    (G ◌ F).obj A = G.obj (F.obj A) :=
  rfl

@[simp]
theorem Functor.comp_map (G : β ⥤ γ) (F : α ⥤ β) :
    (G ◌ F).map f = G.map (F.map f) :=
  rfl

@[simp]
theorem Functor.id_comp (F : α ⥤ β) : 𝟭 β ◌ F = F :=
  by aesop

@[simp]
theorem Functor.comp_id (F : α ⥤ β) : F ◌ 𝟭 α = F :=
  by aesop

@[simp]
theorem Functor.comp_assoc (H : γ ⥤ δ) (G : β ⥤ γ) (F : α ⥤ β) :
    (H ◌ G) ◌ F = H ◌ G ◌ F :=
  by aesop

structure Bundled (c : Type u → Type v) : Type max (u + 1) v where
  α : Type u
  str : c α := by infer_instance

namespace Bundled

attribute [coe] α

set_option checkBinderAnnotations false in
def of {c : Type u → Type v} (α : Type u) [str : c α] : Bundled c :=
  ⟨α, str⟩

instance coeSort : CoeSort (Bundled c) (Type u) :=
  ⟨Bundled.α⟩

theorem coe_mk (α) (str) : (@Bundled.mk c α str : Type u) = α :=
  rfl

def map (f : ∀ {α}, c α → d α) (b : Bundled c) : Bundled d :=
  ⟨b, f b.str⟩

end Bundled

abbrev Cat.{v, u} := Bundled Category.{v, u}

instance : Coe Cat.{v, u} (Type u) where
  coe := Bundled.α

instance (α : Cat.{v, u}) : Category.{v, u} α :=
  α.str

instance : Category (Cat.{v, u}) where
  Hom α β := α ⥤ β
  id α := 𝟭 α
  comp G F := G ◌ F
  id_comp' := by simp
  comp_id' := by simp
  assoc' := by simp

def Functor.opposite (F : α ⥤ β) : αᵒᵖ ⥤ βᵒᵖ where
  obj A := op (F.obj A.unop)
  map f := F.map f
  map_id := F.map_id
  map_comp g f := F.map_comp f g

@[simp]
theorem Functor.opposite_obj (F : α ⥤ β) (A : αᵒᵖ) :
    F.opposite.obj A = op (F.obj A.unop) :=
  rfl

@[simp]
theorem Functor.opposite_map (F : α ⥤ β) {A B : αᵒᵖ} (f : A ⟶ B) :
    F.opposite.map f = F.map f :=
  rfl

@[simp]
theorem Functor.opposite_id :
    (𝟭 α).opposite = 𝟭 αᵒᵖ :=
  rfl

def Op : Cat ⥤ Cat where
  obj α := Bundled.of αᵒᵖ
  map f := f.opposite
  map_id := rfl
  map_comp _ _ := rfl

@[ext]
structure NatTrans {α : Type u₁} {β : Type u₂} [Category.{v₁} α] [Category.{v₂} β]
    (F G : α ⥤ β) : Type (max u₁ v₂) where
  app (A : α) : F.obj A ⟶ G.obj A
  naturality {A B : α} (f : A ⟶ B) :
    app B ∘ F.map f = G.map f ∘ app A

attribute [simp] NatTrans.naturality

def NatTrans.id (F : α ⥤ β) : NatTrans F F where
  app A := 𝟙 (F.obj A)
  naturality f := by simp

@[simp]
theorem NatTrans.id_app (F : α ⥤ β) (A : α) :
    (NatTrans.id F).app A = 𝟙 (F.obj A) :=
  rfl

def NatTrans.comp {F G H : α ⥤ β} (η₁ : NatTrans G H) (η₂ : NatTrans F G) :
    NatTrans F H where
  app A := η₁.app A ∘ η₂.app A
  naturality {A B} f := by
    dsimp only
    rw [assoc, naturality, ← assoc, naturality, assoc]

@[simp]
theorem NatTrans.comp_app {F G H : α ⥤ β}
    (η₁ : NatTrans G H) (η₂ : NatTrans F G) (A : α) :
    (η₁.comp η₂).app A = η₁.app A ∘ η₂.app A :=
  rfl

theorem NatTrans.id_comp {F G : α ⥤ β} (η : NatTrans F G) :
    (NatTrans.id G).comp η = η :=
  by ext; simp

theorem NatTrans.comp_id {F G : α ⥤ β} (η : NatTrans F G) :
    η.comp (NatTrans.id F) = η :=
  by ext; simp

theorem NatTrans.comp_assoc {F G H K : α ⥤ β}
    (η₁ : NatTrans H K) (η₂ : NatTrans G H) (η₃ : NatTrans F G) :
    (η₁.comp η₂).comp η₃ = η₁.comp (η₂.comp η₃) :=
  by ext; simp

def NatTrans.power : NatTrans (𝟭 (Type u)) Power.{u} where
  app α x := ({x} : Set α)
  naturality f := by funext; simp

instance (α : Type u₁) (β : Type u₂) [Category.{v₁, u₁} α] [Category.{v₂, u₂} β] :
    Category (α ⥤ β) where
  Hom := NatTrans
  id := NatTrans.id
  comp := NatTrans.comp
  id_comp' := NatTrans.id_comp
  comp_id' := NatTrans.comp_id
  assoc' := NatTrans.comp_assoc

end Category
