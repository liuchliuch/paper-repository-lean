import Paper18.Category.GraphPicardMoritaCentralLinear
import Paper18.Category.GraphPicardMoritaAdjointCommutative
import Paper18.Category.GraphPicardComponentCharacter
import Paper18.Category.GraphPicardOrbit
import Paper18.Category.DrinfeldNoPivotalDimensionBasic

/-! # The actual graph algebra in the actual Morita adjoint unit

Both the right adjoint and the algebra map are constructed on the actual
chosen simple-orbit component. The component character is its actual
restricted algebra action; no Azumaya equivalence is supplied.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u w
namespace Paper18.Category.GraphPicard
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ] [α.IsEquivalence]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

local notation "M" => GraphLagrangian.ModuleOrbit S α
local notation "E" => ModuleAlphaInduction.End Dᴹᵒᵖ M
local notation "R" => GraphLagrangian.underlyingSeparableNoPivotal S α
local notation "hR" => GraphLagrangian.underlying_id_ne_zero S α
local notation "SC" => DrinfeldCoendModules.centerSkeletonNoPivotal S

local instance graphEndFiniteHom' (F G : E) : FiniteDimensional ℂ (F ⟶ G) :=
  SeparableAlgebra.orbitEndFiniteHom R S hR F G
local instance graphEndKernels' : HasKernels E := SeparableAlgebra.orbitEndHasKernels R S hR
local instance graphEndUnitSimple' : Simple (𝟙_ E) := graphEndSimpleUnit S α

/-- The actual underlying functor of the genuine graph central lift. -/
abbrev graphCentralUnderlying : Center D ⥤ E :=
  Morita.centralUnderlying (rightCentralLift D M)

/-- The actual right-adjoint unit algebra, constructed from actual
finite center Hom spaces on the actual chosen graph orbit. -/
def graphAdjointUnit : Center D :=
  DiagonalAlgebra.semisimpleAdjointAlgebra SC (graphCentralUnderlying S α)

instance graphAdjointUnitMonObj : MonObj (graphAdjointUnit S α) :=
  DiagonalAlgebra.semisimpleAdjointAlgebraMonObj SC (graphCentralUnderlying S α)

/-- The genuine reversed central lift makes the actual adjoint algebra
commutative for the original center braiding as well. -/
instance graphAdjointUnitCommMonObj : IsCommMonObj (graphAdjointUnit S α) where
  mul_comm := by
    have h : (β_ (graphAdjointUnit S α) (graphAdjointUnit S α)).inv ≫
        μ[graphAdjointUnit S α] = μ[graphAdjointUnit S α] := by
      letI : BraidedCategory (Center D) := reverseBraiding (Center D)
      letI : (rightCentralLift D M).Braided := rightCentralLiftReverseBraided D M
      letI := Morita.centralAdjointAlgebra_comm SC (rightCentralLift D M)
      exact IsCommMonObj.mul_comm
        (DiagonalAlgebra.semisimpleAdjointAlgebra SC (graphCentralUnderlying S α))
    apply (cancel_epi (β_ (graphAdjointUnit S α) (graphAdjointUnit S α)).inv).mp
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp, h]

/-- Actual connectedness follows from the actual adjunction and the
actual simple unit of this actual component endofunctor category. -/
theorem graphAdjointUnit_connected :
    Module.finrank ℂ (𝟙_ (Center D) ⟶ graphAdjointUnit S α) = 1 :=
  DiagonalAlgebra.semisimpleAdjointAlgebra_connected SC (graphCentralUnderlying S α)

/-- The genuine component algebra character. -/
def graphComponentCharacter : (graphCentralUnderlying S α).obj
    (GraphLagrangian.algebra S α) ⟶ 𝟙_ E :=
  componentCentralCharacter (GraphLagrangian.algebra S α)
    (GraphLagrangian.moduleSkeleton S α) (SeparableAlgebra.orbitLabel R S hR)

local instance graphMappedAlgebra :
    MonObj ((graphCentralUnderlying S α).obj (GraphLagrangian.algebra S α)) :=
  Functor.monObjObj (F := graphCentralUnderlying S α) (GraphLagrangian.algebra S α)

local instance graphComponentCharacterMonHom : IsMonHom (graphComponentCharacter S α) where
  one_hom := by
    change ((𝟙 _ ≫ (rightCentralUnitIso D M).hom) ≫
      (rightCentralAction D M).map η[GraphLagrangian.algebra S α]) ≫
        graphComponentCharacter S α = 𝟙 _
    simpa only [Category.id_comp, Category.assoc] using
      componentCentralCharacter_one (GraphLagrangian.algebra S α)
        (GraphLagrangian.moduleSkeleton S α) (SeparableAlgebra.orbitLabel R S hR)
  mul_hom := by
    change ((𝟙 _ ≫ (rightCentralTensorIso D M _ _).hom) ≫
      (rightCentralAction D M).map μ[GraphLagrangian.algebra S α]) ≫
        graphComponentCharacter S α =
          (graphComponentCharacter S α ⊗ₘ graphComponentCharacter S α) ≫ (λ_ (𝟙_ E)).hom
    simpa only [Category.id_comp, Category.assoc] using
      componentCentralCharacter_mul (GraphLagrangian.algebra S α)
        (GraphLagrangian.moduleSkeleton S α) (SeparableAlgebra.orbitLabel R S hR)

/-- The actual graph algebra maps into the actual Morita adjoint unit by
transposing its actual component action. -/
def graphAlgebraToAdjointUnit : GraphLagrangian.algebra S α ⟶ graphAdjointUnit S α :=
  Morita.characterTranspose SC (graphCentralUnderlying S α) (graphComponentCharacter S α)

instance graphAlgebraToAdjointUnit_isMonHom : IsMonHom (graphAlgebraToAdjointUnit S α) :=
  Morita.characterTranspose_isMonHom SC (graphCentralUnderlying S α) (graphComponentCharacter S α)

/-- The defining character equation is proved by the actual adjunction. -/
@[reassoc] theorem graphAlgebraToAdjointUnit_counit :
    (graphCentralUnderlying S α).map (graphAlgebraToAdjointUnit S α) ≫
      DiagonalAlgebra.semisimpleAdjointAlgebraCounit SC (graphCentralUnderlying S α) =
        graphComponentCharacter S α :=
  Morita.characterTranspose_counit SC (graphCentralUnderlying S α) (graphComponentCharacter S α)

end Paper18.Category.GraphPicard
