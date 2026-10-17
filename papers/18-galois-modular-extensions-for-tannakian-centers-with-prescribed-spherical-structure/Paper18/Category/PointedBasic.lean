import Mathlib.Algebra.Category.FGModuleCat.Colimits
import Mathlib.Algebra.Category.FGModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.CategoryTheory.GradedObject.Braiding
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Linear.Basic
import Paper18.Results.AppendixB

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical

namespace Paper18.Category

/-- Finite-dimensional complex vector spaces graded by a finite group.
Morphisms are families of linear maps, and tensor product is convolution. -/
def PointedVec (A : Type) := GradedObject A (FGModuleCat ℂ)

namespace PointedVec

variable (A : Type) [Fintype A] [AddGroup A]

instance : Category (PointedVec A) :=
  inferInstanceAs (Category (GradedObject A (FGModuleCat ℂ)))

omit [Fintype A] [AddGroup A] in
@[simp] lemma comp_apply {X Y Z : PointedVec A} (f : X ⟶ Y) (g : Y ⟶ Z) (a : A) :
    (f ≫ g) a = f a ≫ g a := rfl

omit [Fintype A] [AddGroup A] in
@[simp] lemma id_apply (X : PointedVec A) (a : A) : (𝟙 X : X ⟶ X) a = 𝟙 (X a) := rfl

instance : MonoidalCategory (PointedVec A) :=
  GradedObject.monoidalCategory

instance : Preadditive (PointedVec A) where
  homGroup X Y := inferInstanceAs (AddCommGroup (∀ a, X a ⟶ Y a))
  add_comp _ _ _ f g h := by funext a; exact Preadditive.add_comp _ _ _ (f a) (g a) (h a)
  comp_add _ _ _ f g h := by funext a; exact Preadditive.comp_add _ _ _ (f a) (g a) (h a)

instance : Linear ℂ (PointedVec A) where
  homModule X Y := inferInstanceAs (Module ℂ (∀ a, X a ⟶ Y a))
  smul_comp _ _ _ r f g := by funext a; exact Linear.smul_comp _ _ _ r (f a) (g a)
  comp_smul _ _ _ f r g := by funext a; exact Linear.comp_smul _ _ _ (f a) r (g a)

instance (X Y : PointedVec A) : FiniteDimensional ℂ (X ⟶ Y) :=
  inferInstanceAs (FiniteDimensional ℂ (∀ a, X a ⟶ Y a))

/-- The one-dimensional vector space concentrated in degree `a`. -/
def simpleObject (a : A) : PointedVec A :=
  (GradedObject.single a).obj (FGModuleCat.of ℂ ℂ)

/-- Identification of the supported fiber, using the same equality decision
as the definition of the concentrated object. -/
def simpleFiberIso (a : A) : (simpleObject A a) a ≅ FGModuleCat.of ℂ ℂ :=
  GradedObject.singleObjApplyIso a (FGModuleCat.of ℂ ℂ)

lemma simpleFiber_isZero (a b : A) (h : b ≠ a) : IsZero ((simpleObject A a) b) :=
  (GradedObject.isInitialSingleObjApply a (FGModuleCat.of ℂ ℂ) b h).isZero

/-- The actual inclusion of a homogeneous tensor summand into convolution. -/
def tensorInclusion (X Y : PointedVec A) (a b k : A) (h : a + b = k) :
    X a ⊗ Y b ⟶ (X ⊗ Y) k :=
  GradedObject.Monoidal.ιTensorObj X Y a b k h

instance tensorInclusion_mono (X Y : PointedVec A) (a b k : A) (h : a + b = k) :
    Mono (tensorInclusion A X Y a b k h) := by
  unfold tensorInclusion GradedObject.Monoidal.ιTensorObj
    GradedObject.ιMapBifunctorMapObj GradedObject.ιMapObj
  infer_instance

@[ext]
lemma tensor_hom_ext (X Y : PointedVec A) {Z : FGModuleCat ℂ} {k : A}
    (f g : (X ⊗ Y) k ⟶ Z)
    (h : ∀ a b (hab : a + b = k),
      tensorInclusion A X Y a b k hab ≫ f = tensorInclusion A X Y a b k hab ≫ g) :
    f = g := GradedObject.Monoidal.tensorObj_ext f g h

end PointedVec
end Paper18.Category
