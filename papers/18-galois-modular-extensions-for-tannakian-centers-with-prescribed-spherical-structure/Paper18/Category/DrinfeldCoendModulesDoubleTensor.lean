import Paper18.Category.DrinfeldCoendModulesTensorDesc

/-! # Actual paired cap generators detect multiplication identities -/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
open DiagonalAlgebra
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- An actual left and right tensor context for the actual cap coend. -/
def leftTensorImage (A Z : D) : DeligneProduct D D ⥤ D :=
  tensorProductFunctor (C := D) ⋙ tensorLeft A ⋙ tensorRight Z

/-- Braided rigidity supplies an actual left pairing objectwise; its
monoidality is not needed for preservation of the actual coend. -/
def leftTensorImage_preservesCoend (A Z : D) :
    PreservesColimit (multispanIndexCoend (capDiagram (D := D))).multispan
      (leftTensorImage A Z) := by
  let p : ExactPairing (dual D A) (dual D (dual D A)) := inferInstance
  letI : ExactPairing (dual D A) A :=
    @exactPairingCongrRight D _ _ (dual D A) A (dual D (dual D A)) p (drinfeldIso A)
  letI := (tensorLeftAdjunction (dual D A) A).isLeftAdjoint
  letI := (tensorRightAdjunction Z (dual D Z)).isLeftAdjoint
  letI := (tensorProductRightAdjunction S).isLeftAdjoint
  unfold leftTensorImage
  infer_instance

lemma injection_left_tensor_hom_ext {A Z W : D} {f g : (A ⊗ algebra S) ⊗ Z ⟶ W}
    (h : ∀ X : D, (A ◁ injection S X) ▷ Z ≫ f = (A ◁ injection S X) ▷ Z ≫ g) :
    f = g := by
  letI := leftTensorImage_preservesCoend S A Z
  apply capGenerator_hom_ext S (leftTensorImage A Z)
  intro X
  change ((A ◁ (tensorProductFunctor (C := D)).map (capGenerator S X)) ▷ Z) ≫ f =
    ((A ◁ (tensorProductFunctor (C := D)).map (capGenerator S X)) ▷ Z) ≫ g
  apply (cancel_epi ((A ◁ (capPairIso (dual D X) X).inv) ▷ Z)).mp
  simpa only [injection, whiskerLeft_comp, comp_whiskerRight, assoc] using h X

/-- Products of the actual cap generators determine all actual
multiplication-action maps. -/
lemma injection_double_tensor_hom_ext {Z W : D} {f g : (algebra S ⊗ algebra S) ⊗ Z ⟶ W}
    (h : ∀ X Y : D, (injection S X ⊗ₘ injection S Y) ▷ Z ≫ f =
      (injection S X ⊗ₘ injection S Y) ▷ Z ≫ g) : f = g := by
  apply (cancel_epi (α_ (algebra S) (algebra S) Z).inv).mp
  apply injection_tensor_hom_ext S
  intro X
  apply (cancel_epi (α_ (dual D X ⊗ X) (algebra S) Z).hom).mp
  simp only [assoc, ← associator_naturality_left_assoc, Iso.hom_inv_id_assoc]
  apply injection_left_tensor_hom_ext S
  intro Y
  simp only [assoc, ← comp_whiskerRight_assoc, ← MonoidalCategory.tensorHom_def']
  exact h X Y

end Paper18.Category.DrinfeldCoendModules
