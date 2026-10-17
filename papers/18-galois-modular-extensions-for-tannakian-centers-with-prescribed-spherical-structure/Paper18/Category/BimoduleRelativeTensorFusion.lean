import Paper18.Category.BimoduleRelativeTensorQuotient
import Paper18.Category.BimoduleRelativeTensorSeparable
import Paper18.Category.SemisimpleAbelian
import Mathlib.CategoryTheory.Bicategory.End

/-! # Actual relative composition in a fusion category

Finite semisimplicity supplies the coequalizers and actual rigidity
supplies preservation. The native endomorphism category is therefore
monoidal under actual relative composition.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u w
namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- Actual native bimodules over one arbitrary algebra form a monoidal
category with the proved relative tensor, associator and unitors. -/
def monoidal [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
    (R : D) [MonObj R] : MonoidalCategory (Native R R) := by
  letI := nativeBicategory (D := D)
  exact inferInstanceAs (MonoidalCategory ((Mon.mk R) ⟶ (Mon.mk R)))

variable [Preadditive D] [Linear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [LeftRigidCategory D] [RightRigidCategory D]
  {ι : Type w} [Fintype ι] (F : FiniteSemisimpleSkeleton D ι)

/-- In an actual rigid finite semisimple category, the existence of all
balancing quotients is derived from actual semisimplicity. -/
def fusionBicategory : Bicategory (Mon D) := by
  letI := F.abelian
  exact nativeBicategory

/-- The native relative composition monoidal structure in the actual
fusion case, with no independently supplied coequalizer hypothesis. -/
def fusionMonoidal (R : D) [MonObj R] : MonoidalCategory (Native R R) := by
  letI := F.abelian
  exact monoidal R

end Paper18.Category.BimoduleRelativeTensor
