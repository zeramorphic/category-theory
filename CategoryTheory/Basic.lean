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
theorem Type.id (α : Type _) :
    𝟙 α = fun x => x :=
  rfl

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

structure Congruence (α : Type _) [Category α] where
  rel (A B : α) : (A ⟶ B) → (A ⟶ B) → Prop
  equivalence (A B : α) : Equivalence (rel A B)
  rel_whisker {A B C : α} (f g : B ⟶ C) (h : A ⟶ B) (fg : rel B C f g) :
    rel A C (f ∘ h) (g ∘ h)
  whisker_rel {A B C : α} (f : B ⟶ C) (g h : A ⟶ B) (fg : rel A B g h) :
    rel A C (f ∘ g) (f ∘ h)

def Congruence.setoid (r : Congruence α) (A B : α) : Setoid (A ⟶ B) where
  r := r.rel A B
  iseqv := r.equivalence A B

structure HomQuotient (r : Congruence α) where
  unquot : α

def HomQuotient.quotObj (r : Congruence α) (A : α) :
    HomQuotient r :=
  ⟨A⟩

def HomQuotient.quotHom (r : Congruence α) {A B : α} (f : A ⟶ B) :
    Quotient (r.setoid A B) :=
  Quotient.mk _ f

theorem HomQuotient.comp_rel {r : Congruence α} {A B C : HomQuotient r}
    (f₁ : B.unquot ⟶ C.unquot) (g₁ : A.unquot ⟶ B.unquot)
    (f₂ : B.unquot ⟶ C.unquot) (g₂ : A.unquot ⟶ B.unquot)
    (hf : r.rel _ _ f₁ f₂) (hg : r.rel _ _ g₁ g₂) :
    Quotient.mk (Congruence.setoid r A.unquot C.unquot) (f₁ ∘ g₁) =
    Quotient.mk (Congruence.setoid r A.unquot C.unquot) (f₂ ∘ g₂) := by
  have h₁ := r.whisker_rel f₁ g₁ g₂ hg
  have h₂ := r.rel_whisker f₁ f₂ g₂ hf
  exact Quotient.sound ((r.equivalence _ _).trans h₁ h₂)

@[simp]
theorem _root_.Quotient.lift₂_mk {α β γ : Sort _} {_ : Setoid α} {_ : Setoid β}
    (f : α → β → γ)
    (h : ∀ (a₁ : α) (a₂ : β) (b₁ : α) (b₂ : β), a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂)
    (a : α) (b : β) :
    Quotient.lift₂ f h (Quotient.mk _ a) (Quotient.mk _ b) = f a b :=
  rfl

instance (r : Congruence α) : Category (HomQuotient r) where
  Hom A B := Quotient (r.setoid A.unquot B.unquot)
  id A := Quotient.mk _ (𝟙 A.unquot)
  comp := Quotient.lift₂ (fun f g => Quotient.mk _ (f ∘ g)) HomQuotient.comp_rel
  id_comp' := by
    intro A B f
    refine Quotient.inductionOn f ?_
    simp
  comp_id' := by
    intro A B f
    refine Quotient.inductionOn f ?_
    simp
  assoc' := by
    intro A B C D f g h
    refine Quotient.inductionOn₃ f g h ?_
    simp

@[simp]
theorem HomQuotient.quotHom_eq_iff (r : Congruence α)
    {A B : α} (f g : A ⟶ B) :
    quotHom r f = quotHom r g ↔ r.rel A B f g := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

@[elab_as_elim]
theorem HomQuotient.inductionOn {r : Congruence α}
    {A B : HomQuotient r} {motive : (A ⟶ B) → Prop}
    (f : A ⟶ B) (h : ∀ f : A.unquot ⟶ B.unquot, motive (quotHom r f)) :
    motive f :=
  Quotient.inductionOn f h

/-- The quotient map into a quotient category. -/
def HomQuotient.quotient (r : Congruence α) : α ⥤ HomQuotient r where
  obj A := quotObj r A
  map f := quotHom r f
  map_id := by aesop
  map_comp := by aesop

@[simp]
theorem HomQuotient.quotient_obj (r : Congruence α) (A : α) :
    (quotient r).obj A = quotObj r A :=
  rfl

@[simp]
theorem HomQuotient.quotient_map (r : Congruence α) {A B : α} (f : A ⟶ B) :
    (quotient r).map f = quotHom r f :=
  rfl

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

@[simp]
theorem Functor.Hom {F G : α ⥤ β} : (F ⟶ G) = NatTrans F G := rfl

@[simp]
theorem Functor.id' {F : α ⥤ β} : 𝟙 F = NatTrans.id F := rfl

@[simp]
theorem Functor.comp' {F G H : α ⥤ β} {η₁ : G ⟶ H} {η₂ : F ⟶ G} :
    η₁ ∘ η₂ = NatTrans.comp η₁ η₂ :=
  rfl

structure Iso (A B : α) where
  toHom : A ⟶ B
  invHom : B ⟶ A
  toHom_invHom : toHom ∘ invHom = 𝟙 B
  invHom_toHom : invHom ∘ toHom = 𝟙 A

infixl:25 " ≃ " => Iso

instance : Coe (A ≃ B) (A ⟶ B) where
  coe := Iso.toHom

def Iso.refl (A : α) : A ≃ A where
  toHom := 𝟙 A
  invHom := 𝟙 A
  toHom_invHom := by simp
  invHom_toHom := by simp

def Iso.symm (f : A ≃ B) : B ≃ A where
  toHom := f.invHom
  invHom := f.toHom
  toHom_invHom := f.invHom_toHom
  invHom_toHom := f.toHom_invHom

@[simp]
theorem Iso.comp_symm (f : A ≃ B) :
    f ∘ (f.symm : B ⟶ A) = 𝟙 B :=
  f.toHom_invHom

@[simp]
theorem Iso.symm_comp (f : A ≃ B) :
    f.symm ∘ (f : A ⟶ B) = 𝟙 A :=
  f.invHom_toHom

def Faithful (F : α ⥤ β) : Prop :=
  ∀ A B : α, ∀ f g : A ⟶ B, F.map f = F.map g → f = g

def Full (F : α ⥤ β) : Prop :=
  ∀ A B : α, ∀ g : F.obj A ⟶ F.obj B, ∃ f : A ⟶ B, F.map f = g

def EssSurjective (F : α ⥤ β) : Prop :=
  ∀ B : β, Nonempty ((A : α) ×' (F.obj A ≃ B))

theorem HomQuotient.quotient_full (r : Congruence α) :
    Full (quotient r) := by
  intro A B g
  refine Quotient.inductionOn g ?_
  intro g
  exact ⟨g, rfl⟩

theorem HomQuotient.quotient_essSurjective (r : Congruence α) :
    EssSurjective (quotient r) := by
  intro B
  exact ⟨⟨B.unquot, Iso.refl _⟩⟩

end Category
