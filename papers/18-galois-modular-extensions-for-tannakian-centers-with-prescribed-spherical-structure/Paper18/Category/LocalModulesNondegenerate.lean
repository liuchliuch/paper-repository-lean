import Paper18.Category.LocalModulesNondegenerateCenter
import Paper18.Category.RelativeTensorPivotal

/-! # Nondegeneracy of actual separable Frobenius condensation -/
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

include S T in
/-- The actual local-module category of a connected separable commutative
algebra with an actual multiplication pairing and trivial pivotal twist
is Müger nondegenerate when its actual ambient category is nondegenerate.
All module and center structures used here are constructed. -/
theorem localNondegenerate (P : ModuleBalancing.MultiplicationPairing A)
    (J : PivotalStructure C) (hA : (J.twistIso A).hom = 𝟙 A)
    (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1)
    (hC : IsNondegenerate (C := C)) : IsNondegenerate (C := LocalModules A) := by
  letI := S.moduleRightRigid
  letI := S.moduleSimpleUnit T hconnected
  exact S.localNondegenerate_of_modulePivotal T (P.modulePivotal S J hA) hconnected hC

end Paper18.Category.SeparableAlgebra
