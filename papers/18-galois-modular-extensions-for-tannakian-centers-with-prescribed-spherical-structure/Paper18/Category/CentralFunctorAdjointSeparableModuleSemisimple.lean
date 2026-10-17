import Paper18.Category.CentralFunctorAdjointSeparableNativeAverage
import Paper18.Category.CentralFunctorAdjointSeparableOrdinaryTensorSection
import Paper18.Category.InternalModuleAmbientActionLinear
import Paper18.Category.MonoidalOppositeFusion
import Paper18.Category.SemisimpleCokernels

/-! # Actual separability from actual semisimplicity of modules

The actual multiplication tensor map has an ordinary natural section.
The actual separable diagonal algebra averages it to a native module
section. Actual evaluation then gives a genuine two-sided section of the
original algebra multiplication. No pivotal structure is used.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonoidalLeftAction MonObj
universe v u w w'
namespace Paper18.Category.CentralFunctorAdjointSeparable
open MonoidalLeftAction ModuleFunctor.DiagonalAction BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (R : D) [MonObj R]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton (Mod_ D R) κ)
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- An actual finite semisimple module category over an actual braided
fusion category gives an actual separability section of its algebra.
The module skeleton is used only to construct the ordinary section;
module naturality is genuinely proved by diagonal averaging. -/
def separableOfModuleSemisimple : SeparableAlgebra R := by
  letI := S.hasCoequalizers
  letI : RightRigidCategory Dᴹᵒᵖ := MonoidalOppositeFusion.rightRigidCategory
  letI : Simple (𝟙_ Dᴹᵒᵖ) := MonoidalOppositeFusion.simpleUnit
  let SM := MonoidalOppositeFusion.skeleton S
  let P := SeparableAlgebra.freeRegularBimodule R
  let Q := ModuleFunctor.wattsRegular (R := R)
  let F : Ordinary Dᴹᵒᵖ (Mod_ D R) (Mod_ D R) :=
    ofBundled ((tensorRepresentation (R := R) (S := R)).obj P)
  let G : Ordinary Dᴹᵒᵖ (Mod_ D R) (Mod_ D R) :=
    ofBundled ((tensorRepresentation (R := R) (S := R)).obj Q)
  let τ : F ⟶ G := tensorMultiplication R
  letI : ModuleFunctor.IsModuleNatural Dᴹᵒᵖ τ :=
    inferInstanceAs (ModuleFunctor.IsModuleNatural Dᴹᵒᵖ
      (tensorNat (SeparableAlgebra.bimoduleMultiplication R)))
  let s : G ⟶ F := ordinaryTensorMultiplicationSection R T
  let b : G ⟶ F := averageNative SM T s
  letI : ModuleFunctor.IsModuleNatural Dᴹᵒᵖ b := averageNative_moduleNatural SM T s
  apply separableOfModuleNaturalSection R b
  exact averageNative_section SM T τ s (ordinaryTensorMultiplicationSection_id R T)

end Paper18.Category.CentralFunctorAdjointSeparable
