import Paper18.Category.BimoduleRelativeTensorMixedWatts

/-! # Actual mixed Eilenberg--Watts reconstruction and isomorphism reflection -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor.MixedWatts
open ModuleFunctor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  {R S : D} [MonObj R] [MonObj S]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable (Sep : SeparableAlgebra S)

/-- Every genuine strong module functor is recovered as actual relative
tensor with its evaluated native mixed bimodule. -/
def functorTensorIso (F : Bundled Dᴹᵒᵖ (Mod_ D S) (Mod_ D R)) :
    tensorBundled (evaluation.obj F) ≅ F :=
  (evaluationFullyFaithful Sep).preimageIso (tensorIso (evaluation.obj F))

/-- Reconstruction is natural for all genuine module transformations. -/
def functorRoundtripIso : evaluation (R := R) (S := S) ⋙ tensorRepresentation ≅
    𝟭 (Bundled Dᴹᵒᵖ (Mod_ D S) (Mod_ D R)) :=
  NatIso.ofComponents (functorTensorIso Sep) (by
    intro F G τ
    apply (evaluationFullyFaithful Sep).map_injective
    simp only [Functor.map_comp, functorTensorIso, Functor.FullyFaithful.preimageIso_hom,
      Functor.FullyFaithful.map_preimage]
    exact tensorRoundtripIso.hom.naturality (evaluation.map τ))

/-- Actual module natural isomorphisms between the quotient functors
reflect to actual isomorphisms of the two native bimodules. -/
def tensorIsoOfFunctorIso {P Q : Native R S} (e : tensorFunctor P ≅ tensorFunctor Q)
    [IsModuleNatural Dᴹᵒᵖ e.hom] : P ≅ Q :=
  (Functor.FullyFaithful.ofFullyFaithful
    (tensorEquivalence Sep).functor).preimageIso (ModuleFunctor.isoMk e)

end Paper18.Category.BimoduleRelativeTensor.MixedWatts
