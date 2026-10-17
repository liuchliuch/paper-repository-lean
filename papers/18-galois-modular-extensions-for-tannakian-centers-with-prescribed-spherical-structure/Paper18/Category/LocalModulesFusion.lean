import Paper18.Category.LocalModulesSemisimple
import Paper18.Category.RelativeTensorRigid
import Paper18.Category.FusionSubcategoryRigid
import Paper18.Category.FusionSubcategoryIntegral
import Paper18.Category.SemisimpleAbelian

/-! # Actual local fusion categories of connected separable algebras

All local duals are actual ambient module duals: their locality follows
from the finite fusion rules, tensor closure, and summand closure. The
module duals themselves were constructed from free-module retracts.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.SeparableAlgebra
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [HasCoequalizers C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {A : C} [MonObj A] [IsCommMonObj A] (S : SeparableAlgebra A)
  {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton C ι)

/-- Local kernels and the derived actual skeleton give an actual abelian
structure, including actual cokernels and normality. -/
def localAbelian : Abelian (LocalModules A) := by
  letI := S.localHasKernels T
  exact (S.localSkeleton T).abelian

/-- The actual local-module category is right rigid. Dual locality is a
consequence of its actual finite tensor and summand closure. -/
def localRightRigid (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) :
    RightRigidCategory (LocalModules A) := by
  letI := S.moduleRightRigid
  letI := S.moduleSimpleUnit T hconnected
  exact (S.skeleton T).fullSubcategoryRightRigid (localModuleProperty (A := A))

/-- Connectedness also gives a simple unit in the local-module category. -/
def localSimpleUnit (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) :
    Simple (𝟙_ (LocalModules A)) := by
  letI := S.moduleSimpleUnit T hconnected
  exact (S.skeleton T).simple_in_fullSubcategory (localModuleProperty (A := A))
    (𝟙_ (Mod_ C A)) (ObjectProperty.prop_unit _)

section Integral
variable [Simple (𝟙_ C)]

/-- Actual integrality of local modules, stated using their intrinsically
derived FP dimensions and categorical simple objects. -/
def LocalIntegral (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) : Prop :=
  letI := S.localHasKernels T
  letI := S.localRightRigid T hconnected
  letI := S.localSimpleUnit T hconnected
  (S.localSkeleton T).Integral

/-- An integral ambient fusion category yields an integral local fusion
category, via the dominant actual free functor and the actual local inclusion. -/
theorem localIntegral_of_integral (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1)
    (hT : T.Integral) : S.LocalIntegral T hconnected := by
  letI := S.moduleRightRigid
  letI := S.moduleSimpleUnit T hconnected
  have hM : (S.skeleton T).Integral :=
    T.integral_of_dominant (S.skeleton T) (InternalModule.freeFunctor (A := A))
      S.free_retract_dominant hT
  exact (S.skeleton T).fullSubcategoryIntegral_of_integral (localModuleProperty (A := A)) hM

end Integral
end Paper18.Category.SeparableAlgebra
