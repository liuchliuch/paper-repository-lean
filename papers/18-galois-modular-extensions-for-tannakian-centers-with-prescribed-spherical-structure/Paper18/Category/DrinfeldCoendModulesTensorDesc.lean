import Paper18.Category.DrinfeldCoendModulesDesc

/-! # Actual tensor descent for the internal coend algebra -/
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

/-- Tensor product followed by an actual right tensor factor. -/
def tensorImage (Z : D) : DeligneProduct D D ⥤ D :=
  tensorProductFunctor (C := D) ⋙ tensorRight Z

/-- The actual right adjoints supply preservation of the actual cap coend. -/
def tensorImage_preservesCoend (Z : D) :
    PreservesColimit (multispanIndexCoend (capDiagram (D := D))).multispan (tensorImage Z) := by
  letI := (tensorProductRightAdjunction S).isLeftAdjoint
  letI := (tensorRightAdjunction Z (dual D Z)).isLeftAdjoint
  unfold tensorImage
  infer_instance

lemma tensorFamily_dinaturality {Z W : D}
    (k : ∀ X : D, (dual D X ⊗ X) ⊗ Z ⟶ W)
    (hk : ∀ {X Y : D} (f : X ⟶ Y),
      (dualMap D f ▷ X) ▷ Z ≫ k X = (dual D Y ◁ f) ▷ Z ≫ k Y)
    {X Y : D} (f : X ⟶ Y) :
    (tensorImage Z).map (capPairMap (dualMap D f) (𝟙 X)) ≫
        (capPairIso (dual D X) X).hom ▷ Z ≫ k X =
      (tensorImage Z).map (capPairMap (𝟙 (dual D Y)) f) ≫
        (capPairIso (dual D Y) Y).hom ▷ Z ≫ k Y := by
  have h₁ := congrArg (fun q => q ▷ Z) (capPairIso_naturality (dualMap D f) (𝟙 X))
  have h₂ := congrArg (fun q => q ▷ Z) (capPairIso_naturality (𝟙 (dual D Y)) f)
  simp only [comp_whiskerRight, tensorHom_id, id_tensorHom] at h₁ h₂
  change ((tensorProductFunctor (C := D)).map _ ▷ Z) ≫ _ =
    ((tensorProductFunctor (C := D)).map _ ▷ Z) ≫ _
  rw [reassoc_of% h₁, reassoc_of% h₂, hk]

/-- An actual dinatural cap family descends to an actual map out of
L tensor Z; the actual coend law proves the descent. -/
def tensorDesc {Z W : D}
    (k : ∀ X : D, (dual D X ⊗ X) ⊗ Z ⟶ W)
    (hk : ∀ {X Y : D} (f : X ⟶ Y),
      (dualMap D f ▷ X) ▷ Z ≫ k X = (dual D Y ◁ f) ▷ Z ≫ k Y) :
    algebra S ⊗ Z ⟶ W := by
  letI := tensorImage_preservesCoend S Z
  exact capGeneratorDesc S (tensorImage Z)
    (fun X => (capPairIso (dual D X) X).hom ▷ Z ≫ k X)
    (tensorFamily_dinaturality k hk)

@[reassoc]
lemma injection_tensorDesc {Z W : D}
    (k : ∀ X : D, (dual D X ⊗ X) ⊗ Z ⟶ W)
    (hk : ∀ {X Y : D} (f : X ⟶ Y),
      (dualMap D f ▷ X) ▷ Z ≫ k X = (dual D Y ◁ f) ▷ Z ≫ k Y) (X : D) :
    injection S X ▷ Z ≫ tensorDesc S k hk = k X := by
  letI := tensorImage_preservesCoend S Z
  apply (cancel_epi ((capPairIso (dual D X) X).hom ▷ Z)).mp
  have hc : ((capPairIso (dual D X) X).hom ▷ Z) ≫
      ((capPairIso (dual D X) X).inv ▷ Z) = 𝟙 _ := by
    rw [← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight]
  dsimp only [injection, tensorDesc]
  simp only [comp_whiskerRight, assoc, reassoc_of% hc]
  exact capGenerator_desc S (tensorImage Z)
    (fun Y => (capPairIso (dual D Y) Y).hom ▷ Z ≫ k Y)
    (tensorFamily_dinaturality k hk) X

/-- Actual tensor cap generators determine all maps out of L tensor Z. -/
lemma injection_tensor_hom_ext {Z W : D} {f g : algebra S ⊗ Z ⟶ W}
    (h : ∀ X : D, injection S X ▷ Z ≫ f = injection S X ▷ Z ≫ g) : f = g := by
  letI := tensorImage_preservesCoend S Z
  apply capGenerator_hom_ext S (tensorImage Z)
  intro X
  apply (cancel_epi ((capPairIso (dual D X) X).inv ▷ Z)).mp
  simpa only [injection, comp_whiskerRight, assoc] using h X

end Paper18.Category.DrinfeldCoendModules
