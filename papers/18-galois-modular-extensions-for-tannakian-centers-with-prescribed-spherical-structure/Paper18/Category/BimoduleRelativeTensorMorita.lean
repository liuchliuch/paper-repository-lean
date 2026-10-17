import Paper18.Category.BimoduleRelativeTensorMixedWattsReconstruction
import Paper18.Category.BimoduleRelativeTensorFunctorCompositionCoherence

/-! # Actual Morita product isomorphisms reflected from module functors

The input is an actual module natural isomorphism of actual composed
quotient functors. No invertibility or classification conclusion is
assumed for the native bimodules.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor
open ModuleFunctor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  {R S : D} [MonObj R] [MonObj S]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- An actual inverse comparison for the composed module functors
produces the actual left native Morita product isomorphism. -/
def leftInverseIsoOfModuleIso (Sep : SeparableAlgebra R)
    (P : Native R S) (Q : Native S R)
    (e : tensorFunctor Q ⋙ tensorFunctor P ≅ 𝟭 (Mod_ D R))
    [IsModuleNatural Dᴹᵒᵖ e.hom] : tensor P Q ≅ regular R := by
  let c := tensorCompositionIso P Q ≪≫ e ≪≫ (tensorUnitIso R).symm
  letI : IsModuleNatural Dᴹᵒᵖ c.hom := by
    change IsModuleNatural Dᴹᵒᵖ
      ((tensorCompositionIso P Q).hom ≫ e.hom ≫ (tensorUnitIso R).inv)
    infer_instance
  exact MixedWatts.tensorIsoOfFunctorIso Sep c

/-- The other actual inverse comparison produces the actual right
native Morita product isomorphism. -/
def rightInverseIsoOfModuleIso (Sep : SeparableAlgebra S)
    (P : Native R S) (Q : Native S R)
    (e : tensorFunctor P ⋙ tensorFunctor Q ≅ 𝟭 (Mod_ D S))
    [IsModuleNatural Dᴹᵒᵖ e.hom] : tensor Q P ≅ regular S := by
  let c := tensorCompositionIso Q P ≪≫ e ≪≫ (tensorUnitIso S).symm
  letI : IsModuleNatural Dᴹᵒᵖ c.hom := by
    change IsModuleNatural Dᴹᵒᵖ
      ((tensorCompositionIso Q P).hom ≫ e.hom ≫ (tensorUnitIso S).inv)
    infer_instance
  exact MixedWatts.tensorIsoOfFunctorIso Sep c

/-- Conversely, an actual native product contraction gives the actual
inverse comparison of the underlying strong module functors. -/
def moduleIsoOfLeftInverseIso (P : Native R S) (Q : Native S R)
    (e : tensor P Q ≅ regular R) :
    tensorFunctor Q ⋙ tensorFunctor P ≅ 𝟭 (Mod_ D R) :=
  (tensorCompositionIso P Q).symm ≪≫
    (ModuleFunctor.forget (C := Dᴹᵒᵖ) (M := Mod_ D R) (N := Mod_ D R)).mapIso
      (tensorRepresentation.mapIso e) ≪≫ tensorUnitIso R

instance moduleIsoOfLeftInverseIso_moduleNatural (P : Native R S) (Q : Native S R)
    (e : tensor P Q ≅ regular R) :
    IsModuleNatural Dᴹᵒᵖ (moduleIsoOfLeftInverseIso P Q e).hom := by
  change IsModuleNatural Dᴹᵒᵖ
    ((tensorCompositionIso P Q).inv ≫ tensorNat e.hom ≫ (tensorUnitIso R).hom)
  infer_instance

end Paper18.Category.BimoduleRelativeTensor
