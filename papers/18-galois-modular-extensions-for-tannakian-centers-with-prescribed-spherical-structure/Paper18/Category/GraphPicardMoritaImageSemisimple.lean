import Paper18.Category.GraphPicardMoritaImageModules
import Paper18.Category.DrinfeldCoendModulesInverseTransport
import Paper18.Category.SeparableModulesBiproducts
import Paper18.Category.SeparableModulesKernels
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Actual finite semisimplicity of the right-adjoint unit modules

The constructed module equivalence is additive and complex linear. Its
actual images of actual simple representatives and actual biproduct
isomorphisms supply the full module skeleton, without separability as input.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj
universe v u w u' w'
namespace Paper18.Category.GraphPicard.MoritaImage
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasFiniteBiproducts C] [HasKernels C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [RightRigidCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v} D] [Preadditive D] [Linear ℂ D]
  [HasFiniteBiproducts D] [HasKernels D] [MonoidalCategory D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Monoidal]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
open DiagonalAlgebra

/-- The genuine comparison's actual map is the actual right-adjoint map. -/
@[simp] lemma moduleEquivalence_map {X Y : Image F} (f : X ⟶ Y) :
    (((moduleEquivalence S F T).functor.map f).hom).unmop =
      (semisimpleRightAdjoint S F).map f := rfl

instance moduleEquivalence_additive : (moduleEquivalence S F T).functor.Additive where
  map_add {X Y} f g := by
    apply Mod_.Hom.ext
    apply Quiver.Hom.unmop_inj
    change (semisimpleRightAdjoint S F).map (f + g) =
      (semisimpleRightAdjoint S F).map f + (semisimpleRightAdjoint S F).map g
    exact (semisimpleRightAdjoint S F).map_add

instance moduleEquivalence_linear : (moduleEquivalence S F T).functor.Linear ℂ where
  map_smul f r := by
    apply Mod_.Hom.ext
    apply Quiver.Hom.unmop_inj
    change (semisimpleRightAdjoint S F).map (r • f) =
      r • (semisimpleRightAdjoint S F).map f
    exact (semisimpleRightAdjoint S F).map_smul r f

instance moduleEquivalence_inverse_additive : (moduleEquivalence S F T).inverse.Additive :=
  Equivalence.inverse_additive (moduleEquivalence S F T)
instance moduleEquivalence_inverse_linear : (moduleEquivalence S F T).inverse.Linear ℂ :=
  Equivalence.inverseLinear ℂ (moduleEquivalence S F T)

/-- Every actual right-adjoint unit module has the transported actual
finite biproduct decomposition into the transported actual simples. -/
def moduleSkeleton : FiniteSemisimpleSkeleton
    (Mod_ Cᴹᵒᵖ (mop (semisimpleAdjointAlgebra S F))) (SimpleIndex F T) :=
  DrinfeldCoendModules.SkeletonTransport.skeleton (moduleEquivalence S F T).functor
    (skeleton F T)

end Paper18.Category.GraphPicard.MoritaImage
