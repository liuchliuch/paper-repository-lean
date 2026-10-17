import Paper18.Category.QuasiFusionGradedScalar
import Paper18.Category.QuasiFusionCocycle

/-! # Actual degree-dependent convolution associators -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace Paper18.Category.QuasiFusion
variable {A : Type} [Fintype A] [AddGroup A]
open GradedObject.Monoidal

local instance associatorBaseMonoidal : MonoidalCategory (GradedObject A (FGModuleCat ℂ)) :=
  GradedObject.monoidalCategory

/-- The actual convolution associator multiplied by the actual homogeneous scalar. -/
def scalarAssociator (r : A → A → A → ℂˣ) (X Y Z : PointedVec A) :
    (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z) :=
  tripleScalarIso r X Y Z ≪≫ (α_ X Y Z)

@[reassoc (attr := simp)]
lemma inclusion_scalarAssociator (r : A → A → A → ℂˣ) (X Y Z : PointedVec A)
    (a b c k : A) (h : a + b + c = k) :
    ιTensorObj₃' X Y Z a b c k h ≫ (scalarAssociator r X Y Z).hom k =
      (r a b c : ℂ) • ((α_ (X a) (Y b) (Z c)).hom ≫ ιTensorObj₃ X Y Z a b c k h) := by
  change ιTensorObj₃' X Y Z a b c k h ≫
    (tripleScalar (fun a b c => (r a b c : ℂ)) X Y Z k ≫
      (GradedObject.Monoidal.associator X Y Z).hom k) = _
  rw [inclusion_tripleScalar_assoc, ιTensorObj₃'_associator_hom]

@[reassoc (attr := simp)]
lemma inclusion_scalarAssociator_inv (r : A → A → A → ℂˣ) (X Y Z : PointedVec A)
    (a b c k : A) (h : a + b + c = k) :
    ιTensorObj₃ X Y Z a b c k h ≫ (scalarAssociator r X Y Z).inv k =
      (((r a b c)⁻¹ : ℂˣ) : ℂ) •
        ((α_ (X a) (Y b) (Z c)).inv ≫ ιTensorObj₃' X Y Z a b c k h) := by
  change ιTensorObj₃ X Y Z a b c k h ≫
    ((GradedObject.Monoidal.associator X Y Z).inv k ≫
      tripleScalar (fun a b c => (((r a b c)⁻¹ : ℂˣ) : ℂ)) X Y Z k) = _
  rw [ιTensorObj₃_associator_inv_assoc, inclusion_tripleScalar, Linear.comp_smul]

lemma scalarAssociator_naturality (r : A → A → A → ℂˣ)
    {X Y Z X' Y' Z' : PointedVec A} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    ((f ⊗ₘ g) ⊗ₘ h) ≫ (scalarAssociator r X' Y' Z').hom =
      (scalarAssociator r X Y Z).hom ≫ (f ⊗ₘ (g ⊗ₘ h)) := by
  change ((f ⊗ₘ g) ⊗ₘ h) ≫
      (tripleScalar (fun a b c => (r a b c : ℂ)) X' Y' Z' ≫ (α_ X' Y' Z').hom) =
    (tripleScalar (fun a b c => (r a b c : ℂ)) X Y Z ≫ (α_ X Y Z).hom) ≫
      (f ⊗ₘ (g ⊗ₘ h))
  rw [← assoc, tripleScalar_naturality, assoc, MonoidalCategory.associator_naturality, ← assoc]

end Paper18.Category.QuasiFusion
