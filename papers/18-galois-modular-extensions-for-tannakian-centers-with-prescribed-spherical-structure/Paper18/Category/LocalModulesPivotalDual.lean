import Paper18.Category.LocalModulesPivotalFrobenius
import Paper18.Category.RelativeTensorCentralFree

/-! # The underlying perfect pairing of an actual module dual -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u
namespace Paper18.Category.ModuleBalancing
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C] [HasCoequalizers C]
  {A : C} [MonObj A] [IsCommMonObj A]
  [RightRigidCategory (Mod_ C A)]
namespace MultiplicationPairing
variable (P : MultiplicationPairing A)

def freeHomEquiv (X : C) (M : Mod_ C A) :
    (X ⟶ M.X) ≃ (InternalModule.free A X ⟶ M) where
  toFun := InternalModule.freeLift
  invFun f := RelativeTensor.freeUnit X ≫ f.hom
  left_inv f := by simpa only [RelativeTensor.freeUnit, assoc] using InternalModule.unit_freeLift f
  right_inv f := by
    apply RelativeTensor.free_hom_ext
    simpa only [RelativeTensor.freeUnit, assoc] using
      InternalModule.unit_freeLift (RelativeTensor.freeUnit (A := A) X ≫ f.hom)

/-- Rigid currying into a chosen right dual, written as a cap operation. -/
def dualCapEquiv {B : Type*} [Category B] [MonoidalCategory B]
    (X Y Z : B) [ExactPairing Y Z] : (X ⟶ Z) ≃ (X ⊗ Y ⟶ 𝟙_ B) := by
  let e : (X ⟶ Z) ≃ (X ⟶ 𝟙_ B ⊗ Z) :=
    { toFun f := f ≫ (λ_ Z).inv
      invFun f := f ≫ (λ_ Z).hom
      left_inv := by intro f; simp
      right_inv := by intro f; simp }
  exact e.trans (tensorRightHomEquiv X Y Z (𝟙_ B)).symm

lemma dualCapEquiv_apply {B : Type*} [Category B] [MonoidalCategory B]
    {X Y Z : B} [ExactPairing Y Z] (f : X ⟶ Z) :
    dualCapEquiv X Y Z f = f ▷ Y ≫ ε_ Y Z := by
  change (f ≫ (λ_ Z).inv) ▷ Y ≫ (α_ (𝟙_ B) Z Y).hom ≫
    (𝟙_ B) ◁ ε_ Y Z ≫ (ρ_ (𝟙_ B)).hom = _
  monoidal

/-- Compose the actual relative evaluation with the Frobenius counit. -/
def ambientCap (M : Mod_ C A) : (dual (Mod_ C A) M).X ⊗ M.X ⟶ 𝟙_ C :=
  RelativeTensor.π (dual (Mod_ C A) M) M ≫
    (ε_ M (dual (Mod_ C A) M)).hom ≫ P.counit

/-- Free adjunction, actual module rigidity, and Frobenius coinduction
prove that the underlying cap is a perfect pairing. -/
def ambientCapEquiv (M : Mod_ C A) (X : C) :
    (X ⟶ (dual (Mod_ C A) M).X) ≃ (X ⊗ M.X ⟶ 𝟙_ C) := by
  let g := RelativeTensor.freeTensorGenerator (A := A) X M
  let e : ((InternalModule.free A X ⊗ M).X ⟶ 𝟙_ C) ≃
      (X ⊗ M.X ⟶ 𝟙_ C) :=
    { toFun f := g ≫ f
      invFun f := inv g ≫ f
      left_inv := by intro f; simp [g]
      right_inv := by intro f; simp [g] }
  exact (freeHomEquiv X (dual (Mod_ C A) M)).trans
    ((dualCapEquiv (InternalModule.free A X) M (dual (Mod_ C A) M)).trans
      ((P.homToRegularEquiv (InternalModule.free A X ⊗ M)).trans e))

lemma ambientCapEquiv_apply (M : Mod_ C A) (X : C)
    (f : X ⟶ (dual (Mod_ C A) M).X) :
    P.ambientCapEquiv M X f = f ▷ M.X ≫ P.ambientCap M := by
  change RelativeTensor.freeTensorGenerator X M ≫
    (dualCapEquiv (InternalModule.free A X) M (dual (Mod_ C A) M)
      (InternalModule.freeLift f)).hom ≫ P.counit = _
  rw [dualCapEquiv_apply]
  simp only [Mod_.comp_hom', RelativeTensor.freeTensorGenerator, assoc]
  change (RelativeTensor.freeUnit X ▷ M.X) ≫ RelativeTensor.π (InternalModule.free A X) M ≫
    (InternalModule.freeLift f ▷ M).hom ≫ (ε_ M (dual (Mod_ C A) M)).hom ≫ P.counit = _
  rw [RelativeTensor.π_whiskerRight_assoc, ← comp_whiskerRight_assoc]
  have hu : RelativeTensor.freeUnit (A := A) X ≫ (InternalModule.freeLift f).hom = f :=
    by simpa only [RelativeTensor.freeUnit, assoc] using InternalModule.unit_freeLift f
  rw [hu]
  rfl

/-- The underlying object of the chosen module right dual is an actual
ambient right dual, identified by its actual evaluation pairing. -/
def ambientDualIso (M : Mod_ C A) : (dual (Mod_ C A) M).X ≅ dual C M.X := by
  let q := (dualCapEquiv (dual (Mod_ C A) M).X M.X (dual C M.X)).symm (P.ambientCap M)
  let r := (P.ambientCapEquiv M (dual C M.X)).symm (ε_ M.X (dual C M.X))
  have hq : q ▷ M.X ≫ ε_ M.X (dual C M.X) = P.ambientCap M := by
    rw [← dualCapEquiv_apply]
    exact (dualCapEquiv _ _ _).apply_symm_apply _
  have hr : r ▷ M.X ≫ P.ambientCap M = ε_ M.X (dual C M.X) := by
    rw [← P.ambientCapEquiv_apply]
    exact (P.ambientCapEquiv _ _).apply_symm_apply _
  refine ⟨q, r, ?_, ?_⟩
  · apply (P.ambientCapEquiv M (dual (Mod_ C A) M).X).injective
    simp only [P.ambientCapEquiv_apply, comp_whiskerRight, assoc, hr, hq,
      id_whiskerRight, id_comp]
  · apply (dualCapEquiv (dual C M.X) M.X (dual C M.X)).injective
    simp only [dualCapEquiv_apply, comp_whiskerRight, assoc, hq, hr,
      id_whiskerRight, id_comp]

lemma ambientDualIso_evaluation (M : Mod_ C A) :
    (P.ambientDualIso M).hom ▷ M.X ≫ ε_ M.X (dual C M.X) = P.ambientCap M := by
  change ((dualCapEquiv _ _ _).symm (P.ambientCap M)) ▷ M.X ≫ _ = _
  rw [← dualCapEquiv_apply]
  exact (dualCapEquiv _ _ _).apply_symm_apply _

/-- The actual ambient dual comparison is natural in actual module maps. -/
lemma ambientDualIso_naturality {M N : Mod_ C A} (f : M ⟶ N) :
    (dualMap (Mod_ C A) f).hom ≫ (P.ambientDualIso M).hom =
      (P.ambientDualIso N).hom ≫ dualMap C f.hom := by
  apply pairing_hom_ext (inferInstanceAs (ExactPairing M.X (dual C M.X)))
  simp only [comp_whiskerRight, assoc]
  rw [P.ambientDualIso_evaluation, rightAdjointMate_comp_evaluation f.hom,
    ← whisker_exchange_assoc, P.ambientDualIso_evaluation]
  have hc := rightAdjointMate_comp_evaluation f
  have hh := congrArg (fun t => RelativeTensor.π (dual (Mod_ C A) N) M ≫
    t.hom ≫ P.counit) hc
  simp only [Mod_.comp_hom', assoc] at hh
  rw [RelativeTensor.π_whiskerRight_assoc, RelativeTensor.π_whiskerLeft_assoc] at hh
  exact hh

end MultiplicationPairing
end Paper18.Category.ModuleBalancing
