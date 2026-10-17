import Paper18.Category.LocalModulesCenterLinear
import Paper18.Category.LocalModulesCentralizerNondegenerate
import Paper18.Category.RelativeTensorCentralFreeFullyFaithful
import Paper18.Category.LocalModulesFusion
import Paper18.Category.DrinfeldGeneralNondegenerate
import Paper18.Category.DrinfeldPivotal
import Paper18.Category.DrinfeldSemisimple

/-! # Actual local-module nondegeneracy through the constructed centralizer equivalence -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.SeparableAlgebra
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [HasCoequalizers C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {A : C} [MonObj A] [IsCommMonObj A] (S : SeparableAlgebra A)
  {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton C ι)
  [RightRigidCategory (Mod_ C A)] [Simple (𝟙_ (Mod_ C A))]
open RelativeTensor

include S T in
/-- Once the actual module pivotal structure has been constructed, actual
local nondegeneracy follows from the actual general-center theorem,
fully faithful central free image, double centralizer theorem, and local
centralizer equivalence. -/
theorem localNondegenerate_of_modulePivotal (JM : PivotalStructure (Mod_ C A))
    (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1)
    (hC : IsNondegenerate (C := C)) : IsNondegenerate (C := LocalModules A) := by
  letI := Drinfeld.pivotalLeftRigidCategory JM
  let Z := Drinfeld.centerSkeleton (S.skeleton T) JM
  let ff := centralFreeFunctorFullyFaithful T hC hconnected
  letI := ff.full
  letI := ff.faithful
  have hZ := Drinfeld.center_nondegenerate (S.skeleton T) JM
  have hc : IsNondegenerate (C := FreeImageCentralizer A) :=
    centralizerImage_nondegenerate Z (Drinfeld.centerPivotal JM)
      (centralFreeFunctor (A := A)) hZ hC
  have hr : @IsNondegenerate (LocalModules A) _ _ (reverseBraiding (LocalModules A)) _ _ := by
    letI := reverseBraiding (LocalModules A)
    letI := S.localCentralizerFunctorBraidedReverse
    exact nondegenerate_of_braided_equivalence S.localCentralizerFunctor hc
  exact nondegenerate_reverse_iff.mp hr

end Paper18.Category.SeparableAlgebra
