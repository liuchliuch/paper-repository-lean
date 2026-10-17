import Paper18.Category.DiagonalAlgebraTransport
import Paper18.Category.DeligneProductMapReverse
import Paper18.Category.FactorizationFullyFaithful

/-! # The actual graph algebra of a braided tensor autoequivalence

The algebra is the image of the actual canonical diagonal under the
componentwise functor (identity, α), followed by actual central factorization.
Its multiplication, commutativity and perfect pairing use no pivotal input.
Nondegeneracy is used for full faithfulness and actual connectedness.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.GraphLagrangian
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ] [α.IsEquivalence]

/-- The actual graph tensor functor sends a pure pair (X,Y) to the positive
central image of X tensored with the negative central image of α(Y). -/
def graphFunctor : DeligneProduct D D ⥤ Center D :=
  DeligneProduct.map (𝟭 D) α ⋙ Drinfeld.deligneFactorization D

instance graphFunctor_additive : (graphFunctor α).Additive := by
  unfold graphFunctor
  infer_instance
instance graphFunctor_linear : (graphFunctor α).Linear ℂ := by
  unfold graphFunctor
  infer_instance
instance graphFunctor_monoidal : (graphFunctor α).Monoidal := by
  unfold graphFunctor
  infer_instance

/-- Its actual braiding uses the explicitly reversed second source factor. -/
def graphFunctorBraided :
    letI : BraidedCategory (DeligneProduct D D) := Drinfeld.deligneReverseSecondBraiding D
    (graphFunctor α).Braided := by
  letI : BraidedCategory (DeligneProduct D D) := Drinfeld.deligneReverseSecondBraiding D
  letI : (DeligneProduct.map (𝟭 D) α).Braided :=
    DeligneProduct.mapReverseSecondBraided (𝟭 D) α
  letI : (Drinfeld.deligneFactorization D).Braided := Drinfeld.deligneFactorizationBraided D
  unfold graphFunctor
  infer_instance

include S in
/-- Actual Müger nondegeneracy gives full faithfulness of the graph tensor
functor; no pivotal structure or center equivalence is an input. -/
def graphFunctorFullyFaithful (hD : IsNondegenerate (C := D)) :
    (graphFunctor α).FullyFaithful := by
  letI := (Drinfeld.deligneFactorizationFullyFaithful S hD).full
  letI := (Drinfeld.deligneFactorizationFullyFaithful S hD).faithful
  letI : (graphFunctor α).Full := by unfold graphFunctor; infer_instance
  letI : (graphFunctor α).Faithful := by unfold graphFunctor; infer_instance
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- The actual central graph algebra, with its actual multiplication
transported by the constructed strong tensor functor. -/
def algebra : Center D := DiagonalAlgebra.mappedCanonicalAlgebra S (graphFunctor α)

instance algebraMonObj : MonObj (algebra S α) :=
  DiagonalAlgebra.mappedCanonicalAlgebraMonObj S (graphFunctor α)

/-- The multiplication is actually commutative in the Drinfeld center. -/
instance algebraCommMonObj : IsCommMonObj (algebra S α) := by
  letI : BraidedCategory (DeligneProduct D D) := Drinfeld.deligneReverseSecondBraiding D
  letI : (graphFunctor α).Braided := graphFunctorBraided α
  exact DiagonalAlgebra.mappedCanonicalAlgebra_commutative S (graphFunctor α)
    (fun X Y => Functor.LaxBraided.braided (F := graphFunctor α) X Y)

/-- The graph multiplication has a constructed actual nondegenerate cap
and an actual cup, satisfying both triangle identities. -/
def multiplicationPairing : ModuleBalancing.MultiplicationPairing (algebra S α) :=
  DiagonalAlgebra.mappedCanonicalMultiplicationPairing S (graphFunctor α)

/-- The actual multiplication pairing's counit is normalized by the unit. -/
lemma pairing_one_counit :
    η[algebra S α] ≫ (multiplicationPairing S α).counit = 𝟙 _ :=
  DiagonalAlgebra.mappedCanonicalPairing_one_counit S (graphFunctor α)

/-- The actual graph algebra is connected under actual Müger
nondegeneracy, by full faithfulness on the actual unit Hom space. -/
theorem connected (hD : IsNondegenerate (C := D)) :
    Module.finrank ℂ (𝟙_ (Center D) ⟶ algebra S α) = 1 := by
  letI := (graphFunctorFullyFaithful S α hD).full
  letI := (graphFunctorFullyFaithful S α hD).faithful
  exact DiagonalAlgebra.mappedCanonicalAlgebra_connected S (graphFunctor α)

/-- Its actual object is the actual finite sum of graph pairs. -/
def decompositionIso : algebra S α ≅
    ⨁ fun i : ι => (graphFunctor α).obj
      (DeligneProduct.pairObject S S i (S.dualLabel i)) :=
  DiagonalAlgebra.mappedCanonicalAlgebraIso S (graphFunctor α)

/-- The intrinsic FP dimension after actual faithful forgetting is the
ambient category's actual total FP dimension, without a pivotal input. -/
theorem underlying_fpdim : S.fpdim (algebra S α).1 = S.fusionBasis.totalFPdim := by
  change S.fpdim (DiagonalAlgebra.mappedCanonicalAlgebra S
    (graphFunctor α ⋙ Center.forget D)) = S.fusionBasis.totalFPdim
  exact DiagonalAlgebra.mappedCanonicalAlgebra_fpdim S
    (graphFunctor α ⋙ Center.forget D) S

end Paper18.Category.GraphLagrangian
