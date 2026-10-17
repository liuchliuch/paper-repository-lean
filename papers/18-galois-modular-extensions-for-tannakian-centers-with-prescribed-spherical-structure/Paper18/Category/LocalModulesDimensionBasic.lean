import Paper18.Category.LocalModulesNondegenerateCenter
import Paper18.Category.RelativeTensorCentralDimensionBasic
import Paper18.Category.RelativeTensorDimension
import Paper18.Category.DrinfeldDimension

/-! # Intrinsic dimension of the constructed local centralizer -/
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
open RelativeTensor

/-- Intrinsic total FP dimension of the actual local fusion category. -/
def localTotalFPdim (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) : ℝ :=
  letI := S.localHasKernels T
  letI := S.localRightRigid T hconnected
  letI := S.localSimpleUnit T hconnected
  (S.localSkeleton T).fusionBasis.totalFPdim

variable [RightRigidCategory (Mod_ C A)] [Simple (𝟙_ (Mod_ C A))]

omit [Simple (𝟙_ C)] in
/-- The actual local centralizer equivalence identifies intrinsic total
FP dimensions, independently of any centralizer dimension formula. -/
theorem localTotalFPdim_eq_centralizer (JM : PivotalStructure (Mod_ C A))
    (hconnected : Module.finrank ℂ (𝟙_ C ⟶ A) = 1) :
    S.localTotalFPdim T hconnected =
      (letI := Drinfeld.pivotalLeftRigidCategory JM
       (Drinfeld.centerSkeleton (S.skeleton T) JM).centralizerFPdim
         (Set.range (centralFreeFunctor (A := A)).obj)) := by
  letI := Drinfeld.pivotalLeftRigidCategory JM
  let Z := Drinfeld.centerSkeleton (S.skeleton T) JM
  let R := Set.range (centralFreeFunctor (A := A)).obj
  letI := S.localHasKernels T
  letI := S.localRightRigid T hconnected
  letI := S.localSimpleUnit T hconnected
  letI := Z.fullSubcategoryHasKernels (centralizerProperty R)
  letI := Z.fullSubcategoryRightRigid (centralizerProperty R)
  letI := Z.fullSubcategorySimpleUnit (centralizerProperty R)
  letI : ∀ X Y : (centralizerProperty R).FullSubcategory,
      FiniteDimensional ℂ (X ⟶ Y) :=
    fun X Y => inferInstanceAs (FiniteDimensional ℂ (X.obj ⟶ Y.obj))
  change (S.localSkeleton T).fusionBasis.totalFPdim = Z.centralizerFPdim R
  rw [Z.centralizerFPdim_eq_intrinsic]
  exact totalFPdim_eq_of_equivalence (S.localSkeleton T) (Z.centralizerSkeleton R)
    S.localCentralizerFunctor

end Paper18.Category.SeparableAlgebra
