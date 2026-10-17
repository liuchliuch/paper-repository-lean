import Paper18.Category.ModuleBalancingCoherence
import Paper18.Category.SphericalizationFunctor
import Paper18.Category.LocalModulesFree

/-! # The free functor preserves the actual descended pivotal structure -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u v₁ u₁
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual

/-- For actual braided tensor functors, preservation of the actual twists
implies preservation of the pivotal identifications through the canonical
double-dual comparison. -/
lemma preservesPivotal_of_twist
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    [BraidedCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [RightRigidCategory D]
    [BraidedCategory D] (F : C ⥤ D) [F.Braided]
    (J : PivotalStructure C) (K : PivotalStructure D)
    (h : ∀ X, F.map (J.twistIso X).hom = (K.twistIso (F.obj X)).hom) :
    PreservesPivotal F J K := by
  intro X
  rw [← J.twist_comp_drinfeld X, F.map_comp, assoc, doubleDualComparison_drinfeld]
  exact (congrArg (fun f => f ≫ (drinfeldIso (F.obj X)).hom) (h X)).trans
    (K.twist_comp_drinfeld (F.obj X))

namespace ModuleBalancing
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  (J : PivotalStructure C) {A : C} [MonObj A]
  (hA : (J.twistIso A).hom = 𝟙 A)
  [HasCoequalizers C] [IsCommMonObj A]

/-- The descended twist of a free local module is the free image of the
ambient twist whenever its generator centralizes the algebra. -/
lemma free_twist (X : C) (hX : Centralizes A X) :
    moduleMap J hA (InternalModule.free A X) (localModule_free_of_centralizes X hX) =
      InternalModule.freeMap (J.twistIso X).hom := by
  apply Mod_.Hom.ext
  change (J.twistIso (A ⊗ X)).hom = A ◁ (J.twistIso X).hom
  rw [J.twist_tensor, hA, hX, id_comp, id_tensorHom]

section Transparent
variable [RightRigidCategory (Mod_ C A)] (htransparent : A ∈ mugerCenter (C := C))

lemma modulePivotal_twist :
    letI := moduleBraidedOfTransparent htransparent
    (modulePivotal J hA htransparent).twistNatIso = moduleTwist J hA htransparent := by
  letI := moduleBraidedOfTransparent htransparent
  exact pivotalOfBalancing_twist _ _ _

/-- The actual strong braided free functor preserves the descended pivotal
structure. This follows from actual twist preservation and Drinfeld
comparison uniqueness; no trace-preservation field is assumed. -/
theorem free_preservesPivotal :
    letI := moduleBraidedOfTransparent htransparent
    PreservesPivotal (InternalModule.freeFunctor (A := A)) J
      (modulePivotal J hA htransparent) := by
  letI := moduleBraidedOfTransparent htransparent
  letI := RelativeTensor.freeFunctorBraidedOfTransparent htransparent
  apply preservesPivotal_of_twist
  intro X
  have ht := congrArg (fun θ : 𝟭 (Mod_ C A) ≅ 𝟭 (Mod_ C A) => θ.hom.app
    (InternalModule.free A X)) (modulePivotal_twist J hA htransparent)
  change InternalModule.freeMap (J.twistIso X).hom =
    (modulePivotal J hA htransparent).twistNatIso.hom.app (InternalModule.free A X)
  dsimp only at ht
  rw [ht]
  exact (free_twist J hA X (htransparent X (Set.mem_univ X))).symm

end Transparent
end ModuleBalancing
end Paper18.Category
