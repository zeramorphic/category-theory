import Std
import Aesop

-- Copied from Mathlib/Init/Set.lean

structure Set (α : Type _) where
  mem : α → Prop

def setOf {α : Type u} (p : α → Prop) : Set α :=
  ⟨p⟩

namespace Set

instance : Membership α (Set α) where
  mem a s := s.mem a

@[ext]
theorem ext {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b := by
  rw [mk.injEq]
  funext x
  exact propext (h x)

protected def Subset (s₁ s₂ : Set α) :=
  ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂

instance : HasSubset (Set α) :=
  ⟨Set.Subset⟩

instance : EmptyCollection (Set α) where
  emptyCollection := ⟨fun _ => False⟩

open Std.ExtendedBinder in
syntax "{" extBinder " | " term "}" : term

macro_rules
  | `({ $x:ident | $p }) => `(setOf fun $x:ident ↦ $p)
  | `({ $x:ident : $t | $p }) => `(setOf fun $x:ident : $t ↦ $p)
  | `({ $x:ident $b:binderPred | $p }) =>
    `(setOf fun $x:ident ↦ satisfies_binder_pred% $x $b ∧ $p)

@[app_unexpander setOf]
def setOf.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident ↦ $p) => `({ $x:ident | $p })
  | `($_ fun ($x:ident : $ty:term) ↦ $p) => `({ $x:ident : $ty:term | $p })
  | _ => throw ()

open Std.ExtendedBinder in
macro (priority := low) "{" t:term " | " bs:extBinders "}" : term =>
  `({x | ∃ᵉ $bs:extBinders, $t = x})

@[simp]
theorem mem_setOf (p : α → Prop) :
    x ∈ {x | p x} ↔ p x :=
  Iff.rfl

def univ : Set α := {_a | True}

protected def insert (a : α) (s : Set α) : Set α := {b | b = a ∨ b ∈ s}

instance : Insert α (Set α) := ⟨Set.insert⟩

protected def singleton (a : α) : Set α := {b | b = a}

instance instSingletonSet : Singleton α (Set α) := ⟨Set.singleton⟩

protected def union (s₁ s₂ : Set α) : Set α := {a | a ∈ s₁ ∨ a ∈ s₂}

instance : Union (Set α) := ⟨Set.union⟩

protected def inter (s₁ s₂ : Set α) : Set α := {a | a ∈ s₁ ∧ a ∈ s₂}

instance : Inter (Set α) := ⟨Set.inter⟩

protected def compl (s : Set α) : Set α := {a | a ∉ s}

protected def diff (s t : Set α) : Set α := {a ∈ s | a ∉ t}

instance : SDiff (Set α) := ⟨Set.diff⟩

def image (f : α → β) (s : Set α) : Set β := {f a | a ∈ s}

@[simp]
theorem image_id (s : Set α) : image id s = s := by
  ext
  rw [image]
  simp

@[simp]
theorem image_comp (g : β → γ) (f : α → β) (s : Set α) :
    image (g ∘ f) s = image g (image f s) := by
  ext
  unfold image
  aesop

def preimage (f : α → β) (s : Set β) : Set α := {a | f a ∈ s}

@[simp]
theorem preimage_id (s : Set α) : preimage id s = s := rfl

@[simp]
theorem preimage_comp (g : β → γ) (f : α → β) (s : Set γ) :
    preimage (g ∘ f) s = preimage f (preimage g s) :=
  rfl

end Set
