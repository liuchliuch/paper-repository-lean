import Paper18.Category.ModuleBalancingBasic

/-! # Actual quotient proofs of module unit and balancing coherence -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u
namespace Paper18.Category.ModuleBalancing
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  (J : PivotalStructure C) {A : C} [MonObj A]
  (hA : (J.twistIso A).hom = 𝟙 A)
  [HasCoequalizers C] [IsCommMonObj A]

lemma localTwist_unit : (localTwist J hA).hom.app (𝟙_ (LocalModules A)) =
    𝟙 (𝟙_ (LocalModules A)) := by
  apply Mod_.Hom.ext
  exact hA

/-- Balancing descends through the actual relative-tensor quotient. -/
lemma localTwist_tensor (M N : LocalModules A) :
    (localTwist J hA).hom.app (M ⊗ N) =
      (doubleBraiding M N).hom ≫
        ((localTwist J hA).hom.app M ⊗ₘ (localTwist J hA).hom.app N) := by
  apply Mod_.Hom.ext
  apply (cancel_epi (RelativeTensor.π M.obj N.obj)).mp
  simp only [doubleBraiding, Iso.trans_hom, assoc]
  change RelativeTensor.π M.obj N.obj ≫ (J.twistIso (M ⊗ N).obj.X).hom =
    RelativeTensor.π M.obj N.obj ≫ (β_ M N).hom.hom ≫ (β_ N M).hom.hom ≫
      ((moduleMap J hA M.obj M.property) ⊗ₘ (moduleMap J hA N.obj N.property)).hom
  rw [π_localModulesBraiding_assoc, π_localModulesBraiding_assoc,
    ModuleTensorCharacters.tensor_quotient]
  have hn := J.twistNatIso.hom.naturality (RelativeTensor.π M.obj N.obj)
  change RelativeTensor.π M.obj N.obj ≫ (J.twistIso (M ⊗ N).obj.X).hom =
    (J.twistIso (M.obj.X ⊗ N.obj.X)).hom ≫ RelativeTensor.π M.obj N.obj at hn
  rw [J.twist_tensor] at hn
  simpa only [doubleBraiding, Iso.trans_hom, assoc, moduleMap] using hn

lemma moduleTwist_unit (htransparent : A ∈ mugerCenter (C := C)) :
    (moduleTwist J hA htransparent).hom.app (𝟙_ (Mod_ C A)) = 𝟙 (𝟙_ (Mod_ C A)) := by
  apply Mod_.Hom.ext
  exact hA

lemma moduleTwist_tensor (htransparent : A ∈ mugerCenter (C := C)) (M N : Mod_ C A) :
    letI := moduleBraidedOfTransparent htransparent
    (moduleTwist J hA htransparent).hom.app (M ⊗ N) =
      (doubleBraiding M N).hom ≫
        ((moduleTwist J hA htransparent).hom.app M ⊗ₘ
          (moduleTwist J hA htransparent).hom.app N) := by
  let M' : LocalModules A := ⟨M, localModule_of_transparent htransparent M⟩
  let N' : LocalModules A := ⟨N, localModule_of_transparent htransparent N⟩
  exact localTwist_tensor J hA M' N'

/-- The actual coherent local-module twist induces a genuine pivotal
structure on the already constructed actual rigid local-module category. -/
def localPivotal [RightRigidCategory (LocalModules A)] : PivotalStructure (LocalModules A) :=
  pivotalOfBalancing (localTwist J hA) (localTwist_unit J hA) (localTwist_tensor J hA)

/-- The actual coherent module twist induces a genuine pivotal structure
over a transparent algebra. No numerical dimension laws are supplied. -/
def modulePivotal [RightRigidCategory (Mod_ C A)]
    (htransparent : A ∈ mugerCenter (C := C)) :
    letI := moduleBraidedOfTransparent htransparent
    PivotalStructure (Mod_ C A) := by
  letI := moduleBraidedOfTransparent htransparent
  exact pivotalOfBalancing (moduleTwist J hA htransparent)
    (moduleTwist_unit J hA htransparent) (moduleTwist_tensor J hA htransparent)

end Paper18.Category.ModuleBalancing
