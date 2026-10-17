import Paper18.Category.DrinfeldCoendModulesInverseEquivalence
import Paper18.Category.RelativeTensorAdjunction
import Paper18.Category.FunctorImage

/-! # Actual center induction without a pivotal structure

The actual free module and the proved center/coend-module equivalence
construct induction and its actual adjunction to the canonical forgetful
functor. The Hom equivalence retains its complex-linear structure.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- Actual induction is the actual free coend module followed by the
constructed actual inverse center equivalence. -/
def inductionNoPivotal : D ⥤ Center D :=
  InternalModule.freeFunctor (A := algebra S) ⋙ fromModules S

@[simp] lemma inductionNoPivotal_obj_fst (X : D) :
    ((inductionNoPivotal S).obj X).1 = algebra S ⊗ X := rfl

/-- The actual no-pivotal induction/forget adjunction. -/
def inductionForgetAdjunctionNoPivotal : inductionNoPivotal S ⊣ Center.forget D :=
  (RelativeTensor.freeForgetAdjunction (A := algebra S)).comp
    (equivalence S).symm.toAdjunction

/-- The actual linear Hom adjunction, derived by composing the actual
center roundtrip, full faithfulness and actual free-module adjunction. -/
def inductionHomLinearEquivNoPivotal (X : D) (Z : Center D) :
    ((inductionNoPivotal S).obj X ⟶ Z) ≃ₗ[ℂ] (X ⟶ Z.1) :=
  (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) ((centerRoundtripIso S).app Z).symm).trans
    ((fullyFaithfulHomLinearEquiv (fromModules S)
      (InternalModule.free (algebra S) X) ((toModules S).obj Z)).symm.trans
        (RelativeTensor.freeHomLinearEquiv X ((toModules S).obj Z)))

lemma finrank_induction_hom_noPivotal (X : D) (Z : Center D) :
    Module.finrank ℂ ((inductionNoPivotal S).obj X ⟶ Z) =
      Module.finrank ℂ (X ⟶ Z.1) :=
  (inductionHomLinearEquivNoPivotal S X Z).finrank_eq

instance inductionNoPivotal_additive : (inductionNoPivotal S).Additive := by
  unfold inductionNoPivotal
  infer_instance

instance inductionNoPivotal_linear : (inductionNoPivotal S).Linear ℂ := by
  unfold inductionNoPivotal
  infer_instance

end Paper18.Category.DrinfeldCoendModules
