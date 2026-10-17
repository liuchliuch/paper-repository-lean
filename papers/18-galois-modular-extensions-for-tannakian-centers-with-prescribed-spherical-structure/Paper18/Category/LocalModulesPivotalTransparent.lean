import Paper18.Category.ModuleBalancingSeparable
import Paper18.Category.LocalModulesFusion
import Paper18.Category.FunctorImage

/-! # Actual positive spherical local modules over transparent algebras -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.ModuleBalancing
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  (J : PivotalStructure C) {A : C} [MonObj A]
  (hA : (J.twistIso A).hom = 𝟙 A)
  [HasCoequalizers C] [IsCommMonObj A]
  [RightRigidCategory (Mod_ C A)] [RightRigidCategory (LocalModules A)]
  (htransparent : A ∈ mugerCenter (C := C))

lemma localPivotal_twist : (localPivotal J hA).twistNatIso = localTwist J hA :=
  pivotalOfBalancing_twist _ _ _

/-- The actual inclusion preserves the independently constructed descended
local braiding and the transparent all-module braiding. -/
def localInclusionBraided :
    letI := moduleBraidedOfTransparent htransparent
    (localModuleProperty (A := A)).ι.Braided := by
  letI := moduleBraidedOfTransparent htransparent
  refine { braided := ?_ }
  intro M N
  change 𝟙 (M.obj ⊗ N.obj) ≫ localBraidingHom M.obj N.obj N.property =
    localBraidingHom M.obj N.obj (localModule_of_transparent htransparent N.obj) ≫
      𝟙 (N.obj ⊗ M.obj)
  simp only [id_comp, comp_id]

/-- Actual local pivotal structure restricts the actual all-module one,
through the inclusion's canonical double-dual comparison. -/
theorem localInclusion_preservesPivotal :
    letI := moduleBraidedOfTransparent htransparent
    PreservesPivotal (localModuleProperty (A := A)).ι
      (localPivotal J hA) (modulePivotal J hA htransparent) := by
  letI := moduleBraidedOfTransparent htransparent
  letI := localInclusionBraided htransparent
  apply preservesPivotal_of_twist
  intro M
  have hs := localPivotal_twist J hA
  have ht := modulePivotal_twist J hA htransparent
  change (localPivotal J hA).twistNatIso.hom.app M =
    (modulePivotal J hA htransparent).twistNatIso.hom.app M.obj
  rw [hs, ht]
  rfl

section Positive
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  (R : SeparableAlgebra A) {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton C ι)
include R T htransparent

/-- Every actual local simple has the positive dimension inherited from the
actual positive condensed module category. -/
theorem localPivotal_positive
    (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) (pJ : J.Positive) :
    letI := R.localHasKernels T
    letI := R.localSimpleUnit T hconnected
    (localPivotal J hA).Positive := by
  letI := R.localHasKernels T
  letI := R.localSimpleUnit T hconnected
  letI := R.moduleSimpleUnit T hconnected
  letI := moduleBraidedOfTransparent htransparent
  letI := localInclusionBraided htransparent
  have hp := modulePivotal_positive R T J hA htransparent hconnected pJ
  have hf := localInclusion_preservesPivotal J hA htransparent
  intro M hM
  letI := hM
  letI : Simple M.obj := (R.skeleton T).simple_map (localModuleProperty (A := A)).ι M
  have hh := hp M.obj inferInstance
  have hd := hf.rightDim_scalar M
  change (modulePivotal J hA htransparent).rightDim M.obj = (localPivotal J hA).rightDim M at hd
  rw [hd] at hh
  exact hh

/-- The actual local pivotal traces are spherical on every actual
endomorphism, by faithful restriction of the proved condensed sphericality. -/
theorem localPivotal_spherical
    (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) (pJ : J.Positive) :
    (localPivotal J hA).Spherical := by
  letI := moduleBraidedOfTransparent htransparent
  exact (localInclusion_preservesPivotal J hA htransparent).spherical_of_faithful
    (modulePivotal_spherical R T J hA htransparent hconnected pJ)

end Positive
end Paper18.Category.ModuleBalancing
