import Paper18.Category.LocalModulesDimension
import Paper18.Category.LocalModulesPivotalSpherical

/-! # Actual modular Frobenius condensation -/
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
include S T

/-- Actual connected separable commutative Frobenius condensation of an
actual modular category is modular for the actual descended pivotal
structure. Its module and local duals are the constructed ones. -/
theorem local_isModular (P : ModuleBalancing.MultiplicationPairing A)
    (J : PivotalStructure C) (hA : (J.twistIso A).hom = 𝟙 A)
    (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) (hJ : IsModular J) :
    letI := S.localRightRigid T hconnected
    IsModular (ModuleBalancing.localPivotal J hA) := by
  letI := S.moduleRightRigid
  letI := S.localRightRigid T hconnected
  exact ⟨ModuleBalancing.localPivotal_spherical_of_multiplicationPairing
      P J hA S T hconnected hJ.1,
    S.localNondegenerate T P J hA hconnected hJ.2⟩

end Paper18.Category.SeparableAlgebra
