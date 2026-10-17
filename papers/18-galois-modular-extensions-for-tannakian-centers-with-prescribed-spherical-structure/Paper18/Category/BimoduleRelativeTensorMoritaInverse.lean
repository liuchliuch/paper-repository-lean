import Paper18.Category.BimoduleRelativeTensorMorita
import Paper18.Category.BimoduleRelativeTensorModuleInverse

/-! # Actual inverse bimodules from actual module functor equivalences -/
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
variable (P : Native R S) [(tensorFunctor P).IsEquivalence]
local instance tensorBundled_isEquivalence : (tensorBundled P).toFunctor.IsEquivalence := by
  change (tensorFunctor P).IsEquivalence
  infer_instance

/-- The inverse bimodule is the actual evaluated strong inverse of the
actual quotient functor. -/
def inverseBimodule : Native S R :=
  MixedWatts.evaluation.obj (ModuleInverse.inverseBundled (tensorBundled P))

def inverseBimoduleFunctorIso (SepR : SeparableAlgebra R) :
    tensorFunctor (inverseBimodule P) ≅ (tensorFunctor P).asEquivalence.inverse :=
  (ModuleFunctor.forget (C := Dᴹᵒᵖ) (M := Mod_ D R) (N := Mod_ D S)).mapIso
    (MixedWatts.functorTensorIso SepR (ModuleInverse.inverseBundled (tensorBundled P)))

instance inverseBimoduleFunctorIso_moduleNatural (SepR : SeparableAlgebra R) :
    letI := ModuleInverse.inverseLeftLinear (C := Dᴹᵒᵖ) (tensorFunctor P).asEquivalence
    IsModuleNatural Dᴹᵒᵖ (inverseBimoduleFunctorIso P SepR).hom := by
  letI := ModuleInverse.inverseLeftLinear (C := Dᴹᵒᵖ) (tensorFunctor P).asEquivalence
  exact (MixedWatts.functorTensorIso SepR
    (ModuleInverse.inverseBundled (tensorBundled P))).hom.property

def inverseBimoduleLeftFunctorIso (SepR : SeparableAlgebra R) :
    tensorFunctor (inverseBimodule P) ⋙ tensorFunctor P ≅ 𝟭 (Mod_ D R) :=
  Functor.isoWhiskerRight (inverseBimoduleFunctorIso P SepR) (tensorFunctor P) ≪≫
    (tensorFunctor P).asEquivalence.counitIso

instance inverseBimoduleLeftFunctorIso_moduleNatural (SepR : SeparableAlgebra R) :
    IsModuleNatural Dᴹᵒᵖ (inverseBimoduleLeftFunctorIso P SepR).hom := by
  letI := ModuleInverse.inverseLeftLinear (C := Dᴹᵒᵖ) (tensorFunctor P).asEquivalence
  letI : IsModuleNatural Dᴹᵒᵖ (tensorFunctor P).asEquivalence.counitIso.hom :=
    ModuleInverse.counit_moduleNatural (C := Dᴹᵒᵖ) (tensorFunctor P).asEquivalence
  change IsModuleNatural Dᴹᵒᵖ
    (Functor.whiskerRight (inverseBimoduleFunctorIso P SepR).hom (tensorFunctor P) ≫
      (tensorFunctor P).asEquivalence.counitIso.hom)
  infer_instance

def inverseBimoduleRightFunctorIso (SepR : SeparableAlgebra R) :
    tensorFunctor P ⋙ tensorFunctor (inverseBimodule P) ≅ 𝟭 (Mod_ D S) :=
  Functor.isoWhiskerLeft (tensorFunctor P) (inverseBimoduleFunctorIso P SepR) ≪≫
    (tensorFunctor P).asEquivalence.unitIso.symm

instance inverseBimoduleRightFunctorIso_moduleNatural (SepR : SeparableAlgebra R) :
    IsModuleNatural Dᴹᵒᵖ (inverseBimoduleRightFunctorIso P SepR).hom := by
  letI := ModuleInverse.inverseLeftLinear (C := Dᴹᵒᵖ) (tensorFunctor P).asEquivalence
  letI : IsModuleNatural Dᴹᵒᵖ (tensorFunctor P).asEquivalence.unitIso.hom :=
    ModuleInverse.unit_moduleNatural (C := Dᴹᵒᵖ) (tensorFunctor P).asEquivalence
  change IsModuleNatural Dᴹᵒᵖ
    (Functor.whiskerLeft (tensorFunctor P) (inverseBimoduleFunctorIso P SepR).hom ≫
      (tensorFunctor P).asEquivalence.unitIso.inv)
  infer_instance

/-- Actual left product contraction, derived from actual categorical
equivalence rather than an inverse-bimodule premise. -/
def inverseBimoduleLeftIso (SepR : SeparableAlgebra R) :
    tensor P (inverseBimodule P) ≅ regular R :=
  leftInverseIsoOfModuleIso SepR P (inverseBimodule P)
    (inverseBimoduleLeftFunctorIso P SepR)

/-- Actual right product contraction. -/
def inverseBimoduleRightIso (SepR : SeparableAlgebra R) (SepS : SeparableAlgebra S) :
    tensor (inverseBimodule P) P ≅ regular S :=
  rightInverseIsoOfModuleIso SepS P (inverseBimodule P)
    (inverseBimoduleRightFunctorIso P SepR)

theorem tensorInverse_of_tensorFunctor_isEquivalence
    (SepR : SeparableAlgebra R) (SepS : SeparableAlgebra S) :
    ∃ Q : Native S R, Nonempty (tensor P Q ≅ regular R) ∧
      Nonempty (tensor Q P ≅ regular S) :=
  ⟨inverseBimodule P, ⟨inverseBimoduleLeftIso P SepR⟩,
    ⟨inverseBimoduleRightIso P SepR SepS⟩⟩

end Paper18.Category.BimoduleRelativeTensor
