import Paper18.Category.GraphPicardCorrected

/-! # The actual ordinary relation between native graph alpha inductions

The actual Drinfeld map removes the double-dual correction as an
ordinary natural isomorphism. This step makes no monoidality claim for
that ordinary comparison. It identifies the genuine essential images
of the two native alpha inductions on the actual graph orbit.
-/
noncomputable section
set_option maxHeartbeats 2000000
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

/-- The actual uncorrected orbit cap is invertible as an ordinary
natural transformation. Only the corrected comparison is monoidal. -/
def graphOrbitCapOrdinaryIso :
    α ⋙ Drinfeld.negative D ⋙ rightCentralAction D (GraphLagrangian.ModuleOrbit S α) ≅
      Drinfeld.positive D ⋙ rightCentralAction D (GraphLagrangian.ModuleOrbit S α) :=
  graphOrbitCapCorrectedIso S α ≪≫
    Functor.isoWhiskerRight (drinfeldNatIso (C := D)).symm
      (Drinfeld.positive D ⋙ rightCentralAction D (GraphLagrangian.ModuleOrbit S α)) ≪≫
    Functor.leftUnitor _

/-- The genuine graph cap identifies the actual two native alpha
inductions after the specified actual self-equivalence and the actual
ordinary monoidal-opposite equivalence. -/
def graphNativeComparisonIso :
    α ⋙ mopFunctor D ⋙ graphPositive S α ≅ mopFunctor D ⋙ graphNegative S α :=
  (Functor.isoWhiskerLeft α
    (rightNegativeNativeIso D (GraphLagrangian.ModuleOrbit S α))).symm ≪≫
      graphOrbitCapOrdinaryIso S α ≪≫
        rightPositiveNativeIso D (GraphLagrangian.ModuleOrbit S α)

/-- The actual two native alpha induction images agree. Fullness and
essential surjectivity are not used in establishing this equality. -/
theorem graphNative_essImage :
    (graphPositive S α).essImage = (graphNegative S α).essImage := by
  have h := Functor.essImage_eq_of_natIso (graphNativeComparisonIso S α)
  simpa only [Functor.essImage_comp_of_essSurj] using h

end Paper18.Category.GraphPicard
