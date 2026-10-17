import Paper18.Category.RigidDoubleDual
import Mathlib.CategoryTheory.Monoidal.Transport

/-!
# The actual category of pivotalized objects

Objects carry an isomorphism to the canonical double dual, and morphisms commute
with it. This is the categorical ambient space in which the Radford square
condition cuts out sphericalization. Neither a pivotal structure on the original
category nor sphericality of the new category is assumed in these definitions.
-/
noncomputable section
universe v u
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
attribute [local instance 2000] RightRigidCategory.rightDual
variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- An actual object together with a chosen double-dual identification. -/
structure Pivotalized where
  obj : C
  phi : obj ≅ (doubleDualFunctor C).obj obj

namespace Pivotalized
variable {C}

/-- Morphisms are exactly the ambient morphisms commuting with the chosen
pivotal identifications. -/
@[ext] structure Hom (X Y : Pivotalized C) where
  hom : X.obj ⟶ Y.obj
  comm : hom ≫ Y.phi.hom = X.phi.hom ≫ (doubleDualFunctor C).map hom

instance : Category (Pivotalized C) where
  Hom := Hom
  id X := ⟨𝟙 X.obj, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    rw [Functor.map_comp, assoc, g.comm, ← assoc, f.comm, assoc]⟩
  id_comp f := Hom.ext (id_comp f.hom)
  comp_id f := Hom.ext (comp_id f.hom)
  assoc f g h := Hom.ext (assoc f.hom g.hom h.hom)

@[simp] lemma id_hom (X : Pivotalized C) : (𝟙 X : X ⟶ X).hom = 𝟙 X.obj := rfl
@[simp] lemma comp_hom {X Y Z : Pivotalized C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- An ambient isomorphism lifts when its forward map commutes with `phi`. -/
def mkIso {X Y : Pivotalized C} (i : X.obj ≅ Y.obj)
    (h : i.hom ≫ Y.phi.hom = X.phi.hom ≫ (doubleDualFunctor C).map i.hom) : X ≅ Y where
  hom := ⟨i.hom, h⟩
  inv := ⟨i.inv, by
    apply (cancel_epi i.hom).1
    simp only [← assoc, Iso.hom_inv_id, id_comp]
    rw [h, assoc, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      comp_id]⟩
  hom_inv_id := Hom.ext i.hom_inv_id
  inv_hom_id := Hom.ext i.inv_hom_id

/-- The faithful forgetful functor to actual ambient objects and morphisms. -/
def forget : Pivotalized C ⥤ C where
  obj X := X.obj
  map f := f.hom

instance : (forget (C := C)).Faithful where
  map_injective h := Hom.ext h

/-- The tensor product of pivotalized objects uses the canonical double-dual
strong monoidal structure constructed from rigidity alone. -/
def tensorObj (X Y : Pivotalized C) : Pivotalized C where
  obj := X.obj ⊗ Y.obj
  phi := (X.phi ⊗ᵢ Y.phi) ≪≫ μIso (doubleDualFunctor C) X.obj Y.obj

/-- The tensor unit with its canonical double-dual identification. -/
def tensorUnit : Pivotalized C where
  obj := 𝟙_ C
  phi := εIso (doubleDualFunctor C)

/-- Tensor product of actual commuting morphisms. -/
def tensorHom {X X' Y Y' : Pivotalized C} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorObj X Y ⟶ tensorObj X' Y' where
  hom := f.hom ⊗ₘ g.hom
  comm := by
    dsimp only [tensorObj, Iso.trans_hom, tensorIso_hom, μIso_hom]
    rw [← assoc, tensorHom_comp_tensorHom, f.comm, g.comm,
      ← tensorHom_comp_tensorHom, assoc, μ_natural]
    simp only [assoc]

/-- The ambient associator commutes with the pivotalized structure. -/
def associator (X Y Z : Pivotalized C) :
    tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) :=
  mkIso (α_ X.obj Y.obj Z.obj) (by
    dsimp only [tensorObj, Iso.trans_hom, tensorIso_hom, μIso_hom]
    rw [← tensorHom_comp_whiskerLeft, ← tensorHom_comp_whiskerRight]
    simp only [assoc]
    rw [← associator_naturality_assoc, Functor.LaxMonoidal.associativity])

/-- The ambient left unitor commutes with the double-dual identifications. -/
def leftUnitor (X : Pivotalized C) : tensorObj (tensorUnit (C := C)) X ≅ X :=
  mkIso (λ_ X.obj) (by
    dsimp only [tensorObj, tensorUnit, Iso.trans_hom, tensorIso_hom,
      μIso_hom, εIso_hom]
    rw [assoc, ← tensorUnit_whiskerLeft_comp_leftUnitor_hom]
    exact (leftUnitor_naturality X.phi.hom).symm)

/-- The ambient right unitor commutes with the double-dual identifications. -/
def rightUnitor (X : Pivotalized C) : tensorObj X (tensorUnit (C := C)) ≅ X :=
  mkIso (ρ_ X.obj) (by
    dsimp only [tensorObj, tensorUnit, Iso.trans_hom, tensorIso_hom,
      μIso_hom, εIso_hom]
    rw [assoc, ← whiskerRight_tensorUnit_comp_rightUnitor_hom]
    exact (rightUnitor_naturality X.phi.hom).symm)

/-- Tensor operations on actual pivotalized objects. -/
instance monoidalStruct : MonoidalCategoryStruct (Pivotalized C) where
  tensorObj := tensorObj
  tensorHom := tensorHom
  whiskerLeft X _ _ f := tensorHom (𝟙 X) f
  whiskerRight f Y := tensorHom f (𝟙 Y)
  tensorUnit := tensorUnit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

/-- The faithful forgetful functor identifies all coherence maps with those
of the original rigid category. -/
def inducingData : Monoidal.InducingFunctorData (forget (C := C)) where
  μIso _ _ := Iso.refl _
  εIso := Iso.refl _
  whiskerLeft_eq := by
    intros
    simp [forget, monoidalStruct, tensorHom]
    erw [Category.id_comp]
  whiskerRight_eq := by
    intros
    simp [forget, monoidalStruct, tensorHom]
    erw [Category.id_comp]
  tensorHom_eq := by
    intros
    simp [forget, monoidalStruct, tensorHom]
    erw [Category.id_comp]
  associator_eq := by
    intros
    simp [forget, monoidalStruct, associator, mkIso, tensorObj, Category.id_comp]
  leftUnitor_eq := by
    intros
    simp [forget, monoidalStruct, leftUnitor, mkIso, tensorUnit]
    erw [Category.id_comp]
  rightUnitor_eq := by
    intros
    simp [forget, monoidalStruct, rightUnitor, mkIso, tensorUnit]
    erw [Category.id_comp]

/-- Monoidal coherence is reflected by the faithful forgetful functor. -/
instance monoidalCategory : MonoidalCategory (Pivotalized C) :=
  Monoidal.induced forget inducingData

/-- Pivotalization has a strong monoidal forgetful functor. -/
instance forget_monoidal : (forget (C := C)).Monoidal :=
  Monoidal.fromInducedMonoidal forget inducingData

@[simp] theorem forget_ε : ε (forget (C := C)) = 𝟙 (𝟙_ C) := rfl
@[simp] theorem forget_η : η (forget (C := C)) = 𝟙 (𝟙_ C) := rfl
@[simp] theorem forget_μ (X Y : Pivotalized C) :
    μ forget X Y = 𝟙 (X.obj ⊗ Y.obj) := rfl
@[simp] theorem forget_δ (X Y : Pivotalized C) :
    δ forget X Y = 𝟙 (X.obj ⊗ Y.obj) := rfl

@[simp] theorem tensorObj_obj (X Y : Pivotalized C) :
    (X ⊗ Y).obj = X.obj ⊗ Y.obj := rfl
@[simp] theorem tensorUnit_obj : (𝟙_ (Pivotalized C)).obj = 𝟙_ C := rfl
@[simp] theorem tensorHom_hom {X X' Y Y' : Pivotalized C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g).hom = f.hom ⊗ₘ g.hom := rfl
@[simp] theorem whiskerLeft_hom (X : Pivotalized C) {Y Z : Pivotalized C} (f : Y ⟶ Z) :
    (X ◁ f).hom = X.obj ◁ f.hom := by
  change (𝟙 X.obj ⊗ₘ f.hom) = _
  simp
@[simp] theorem whiskerRight_hom {X Y : Pivotalized C} (f : X ⟶ Y) (Z : Pivotalized C) :
    (f ▷ Z).hom = f.hom ▷ Z.obj := by
  change (f.hom ⊗ₘ 𝟙 Z.obj) = _
  simp


end Pivotalized
end Paper18.Category
