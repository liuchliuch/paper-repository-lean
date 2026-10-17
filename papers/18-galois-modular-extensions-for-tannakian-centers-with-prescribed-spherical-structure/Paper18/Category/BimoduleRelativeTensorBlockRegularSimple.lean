import Paper18.Category.BimoduleRelativeTensorBlockRegular
import Paper18.Category.ModuleFunctorDualDimensionBlockSimple

/-! # Actual simplicity of the regular quotient-block bimodule -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u w
namespace Paper18.Category.BimoduleRelativeTensor.Block
open ModuleFunctor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {R : D} [MonObj R]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable (Q : Bimodules R) (q : Retract Q (wattsRegular (R := R))) [Simple Q]
  (Sep : SeparableAlgebra R) {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton D ι)

/-- Full faithful two-sided restriction and the actual block identity
transfer the one-dimensional endomorphism space to the regular quotient. -/
def regular_simple : letI := blockMonObj Q q;
    Simple (wattsRegular (R := Q.X.X)) := by
  letI := blockMonObj Q q
  letI := blockProjection_isMonHom Q q
  letI := blockProjection_isSplitEpi Q q
  let SB := blockSeparable Q q Sep
  apply (bimoduleSkeleton SB T).simple_of_finrank_end_eq_one
  rw [(fullyFaithfulHomLinearEquiv (bimoduleRestriction (blockProjection Q q))
    (wattsRegular (R := Q.X.X)) (wattsRegular (R := Q.X.X))).finrank_eq]
  rw [finrank_hom_iso (restrictedRegularIso Q q) (restrictedRegularIso Q q)]
  exact CategoryTheory.finrank_endomorphism_simple_eq_one ℂ Q

/-- The actual algebra of a chosen module orbit has a genuinely simple
regular bimodule, derived without a dimension or connectedness premise. -/
def orbitRegular_simple [BraidedCategory D] [RightRigidCategory D]
    (S : SeparableAlgebra R) (j : S.SimpleIndex T) :
    letI := orbitBlockMonObj S T j
    Simple (wattsRegular (R := (orbitBlockBimodule S T j).X.X)) := by
  letI := orbitBlockBimodule_simple S T j
  exact regular_simple (orbitBlockBimodule S T j) (orbitBlockRetract S T j) S T

end Paper18.Category.BimoduleRelativeTensor.Block
