import Paper18.Category.CentralizerJoin
import Mathlib.CategoryTheory.Monoidal.Transport

/-! # The actual center relative to an actual tensor full subcategory -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- An actual half-braiding tested against every object and morphism of the
specified actual tensor full subcategory. -/
structure RelativeHalfBraiding (P : ObjectProperty C) [P.IsMonoidal] (X : C) where
  β : ∀ U : C, P U → (X ⊗ U ≅ U ⊗ X)
  monoidal : ∀ U V (hU : P U) (hV : P V),
    (β (U ⊗ V) (ObjectProperty.prop_tensor hU hV)).hom =
      (α_ X U V).inv ≫ (β U hU).hom ▷ V ≫ (α_ U X V).hom ≫
        U ◁ (β V hV).hom ≫ (α_ U V X).inv := by cat_disch
  naturality : ∀ {U V : C} (hU : P U) (hV : P V) (f : U ⟶ V),
    X ◁ f ≫ (β V hV).hom = (β U hU).hom ≫ f ▷ X := by cat_disch

attribute [reassoc, simp] RelativeHalfBraiding.monoidal
attribute [reassoc, simp] RelativeHalfBraiding.naturality

/-- Objects of the actual relative center. -/
def RelativeCenter (P : ObjectProperty C) [P.IsMonoidal] := Σ X : C, RelativeHalfBraiding P X

namespace RelativeCenter
variable (P : ObjectProperty C) [P.IsMonoidal]

@[ext] structure Hom (X Y : RelativeCenter P) where
  f : X.1 ⟶ Y.1
  comm : ∀ (U : C) (hU : P U), f ▷ U ≫ (Y.2.β U hU).hom =
    (X.2.β U hU).hom ≫ U ◁ f

attribute [reassoc (attr := simp)] Hom.comm
instance : Quiver (RelativeCenter P) where Hom := Hom P
@[ext] lemma ext {X Y : RelativeCenter P} (f g : X ⟶ Y) (h : f.f = g.f) : f = g := by
  cases f; cases g; congr
instance category : Category (RelativeCenter P) where
  id X := ⟨𝟙 X.1, by intro U hU; simp⟩
  comp f g := ⟨f.f ≫ g.f, by
    intro U hU
    rw [comp_whiskerRight, assoc, g.comm U hU, ← assoc, f.comm U hU, assoc, ← whiskerLeft_comp]⟩

@[simp] lemma id_f (X : RelativeCenter P) : Hom.f (𝟙 X) = 𝟙 X.1 := rfl
@[simp] lemma comp_f {X Y Z : RelativeCenter P} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).f = f.f ≫ g.f := rfl

/-- A relative-central morphism with invertible underlying morphism is invertible. -/
@[simps]
def isoMk {X Y : RelativeCenter P} (f : X ⟶ Y) [IsIso f.f] : X ≅ Y where
  hom := f
  inv := ⟨inv f.f, by
    intro U hU
    simp [f.comm U hU, ← cancel_epi (f.f ▷ U), ← comp_whiskerRight_assoc, ← whiskerLeft_comp]⟩
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

instance isIso_of_f_isIso {X Y : RelativeCenter P} (f : X ⟶ Y) [IsIso f.f] : IsIso f :=
  (isoMk P f).isIso_hom

/-- The actual underlying-object functor of the relative center. -/
def forget : RelativeCenter P ⥤ C where
  obj X := X.1
  map f := f.f

instance forget_faithful : (forget P).Faithful where
  map_injective h := ext P _ _ h

/-- Restrict an actual ambient half-braiding to the actual full subcategory. -/
def restriction : Center C ⥤ RelativeCenter P where
  obj X := ⟨X.1, {
    β := fun U _ => X.2.β U
    monoidal := fun U V _ _ => X.2.monoidal U V
    naturality := fun _ _ f => X.2.naturality f }⟩
  map f := ⟨f.f, fun U _ => f.comm U⟩

@[simp] lemma restriction_obj_fst (X : Center C) : ((restriction P).obj X).1 = X.1 := rfl
@[simp] lemma restriction_obj_β (X : Center C) (U : C) (hU : P U) :
    ((restriction P).obj X).2.β U hU = X.2.β U := rfl
@[simp] lemma restriction_map_f {X Y : Center C} (f : X ⟶ Y) :
    ((restriction P).map f).f = f.f := rfl

end RelativeCenter
end Paper18.Category
