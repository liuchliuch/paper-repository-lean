import Paper18.Category.ModuleBalancingPositive
import Paper18.Category.RelativeTensorRigid

/-! # Positive spherical pivotal structures after transparent condensation -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.ModuleBalancing
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [HasCoequalizers C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {A : C} [MonObj A] [IsCommMonObj A] (R : SeparableAlgebra A)
  {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton C ι)
  (J : PivotalStructure C) (hA : (J.twistIso A).hom = 𝟙 A)
  (htransparent : A ∈ mugerCenter (C := C))
  [RightRigidCategory (Mod_ C A)]
include R T

/-- Connected transparent separable condensation carries the actual positive
pivotal structure descended from the given actual positive structure. -/
theorem modulePivotal_positive
    (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) (pJ : J.Positive) :
    letI := R.moduleSimpleUnit T hconnected
    letI := moduleBraidedOfTransparent htransparent
    (modulePivotal J hA htransparent).Positive := by
  letI := R.moduleSimpleUnit T hconnected
  letI := moduleBraidedOfTransparent htransparent
  exact (free_preservesPivotal J hA htransparent).positive_of_dominant T (R.skeleton T)
    (fun M _ => R.free_retract_dominant M) pJ

/-- Sphericality after transparent positive condensation is proved on every
actual module endomorphism from the derived positive categorical dimensions. -/
theorem modulePivotal_spherical
    (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) (pJ : J.Positive) :
    letI := R.moduleSimpleUnit T hconnected
    letI := moduleBraidedOfTransparent htransparent
    (modulePivotal J hA htransparent).Spherical := by
  letI := R.moduleSimpleUnit T hconnected
  letI := moduleBraidedOfTransparent htransparent
  exact (modulePivotal J hA htransparent).spherical_of_positive (R.skeleton T)
    (modulePivotal_positive R T J hA htransparent hconnected pJ)

end Paper18.Category.ModuleBalancing
