import Paper18.Category.RelativeTensorFree

/-! # Actual ambient tensor actions on internal modules -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory
open scoped MonObj
universe v u
namespace Paper18.Category.RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]

/-- Tensor an actual module morphism with an ambient object. -/
def ambientTensorMap {M N : Mod_ C A} (f : M ⟶ N) (Y : C) :
    ambientTensor M Y ⟶ ambientTensor N Y :=
  Mod_.Hom.mk' (f.hom ▷ Y) (by
    have hf : γ[A,M.X] ≫ f.hom = (A ◁ f.hom) ≫ γ[A,N.X] :=
      IsMod_Hom.smul_hom (A := A) (f := f.hom)
    change ((α_ A M.X Y).inv ≫ γ[A,M.X] ▷ Y) ≫ f.hom ▷ Y =
      (A ◁ f.hom ▷ Y) ≫ (α_ A N.X Y).inv ≫ γ[A,N.X] ▷ Y
    rw [Category.assoc, ← comp_whiskerRight, hf, comp_whiskerRight]
    monoidal)

/-- Tensor an actual module with a morphism of ambient objects. -/
def ambientTensorMapRight (M : Mod_ C A) {X Y : C} (f : X ⟶ Y) :
    ambientTensor M X ⟶ ambientTensor M Y :=
  Mod_.Hom.mk' (M.X ◁ f) (by
    change ((α_ A M.X X).inv ≫ γ[A,M.X] ▷ X) ≫ (M.X ◁ f) =
      (A ◁ M.X ◁ f) ≫ (α_ A M.X Y).inv ≫ γ[A,M.X] ▷ Y
    rw [Category.assoc, ← whisker_exchange, associator_inv_naturality_right_assoc]
    rfl)

/-- Tensor an actual module isomorphism with an ambient object. -/
def ambientTensorIso {M N : Mod_ C A} (e : M ≅ N) (Y : C) :
    ambientTensor M Y ≅ ambientTensor N Y where
  hom := ambientTensorMap e.hom Y
  inv := ambientTensorMap e.inv Y
  hom_inv_id := by
    apply Mod_.Hom.ext
    change e.hom.hom ▷ Y ≫ e.inv.hom ▷ Y = 𝟙 _
    rw [← comp_whiskerRight]
    have h := congrArg Mod_.Hom.hom e.hom_inv_id
    change e.hom.hom ≫ e.inv.hom = 𝟙 _ at h
    rw [h, MonoidalCategory.id_whiskerRight]
  inv_hom_id := by
    apply Mod_.Hom.ext
    change e.inv.hom ▷ Y ≫ e.hom.hom ▷ Y = 𝟙 _
    rw [← comp_whiskerRight]
    have h := congrArg Mod_.Hom.hom e.inv_hom_id
    change e.inv.hom ≫ e.hom.hom = 𝟙 _ at h
    rw [h, MonoidalCategory.id_whiskerRight]

/-- Reassociate the actual ambient tensor of an internal module. -/
def ambientTensorAssoc (M : Mod_ C A) (X Y : C) :
    ambientTensor (ambientTensor M X) Y ≅ ambientTensor M (X ⊗ Y) where
  hom := Mod_.Hom.mk' (α_ M.X X Y).hom (by
    change ((α_ A (M.X ⊗ X) Y).inv ≫
        ((α_ A M.X X).inv ≫ γ[A,M.X] ▷ X) ▷ Y) ≫ (α_ M.X X Y).hom =
      (A ◁ (α_ M.X X Y).hom) ≫ (α_ A M.X (X ⊗ Y)).inv ≫ γ[A,M.X] ▷ (X ⊗ Y)
    monoidal)
  inv := Mod_.Hom.mk' (α_ M.X X Y).inv (by
    change ((α_ A M.X (X ⊗ Y)).inv ≫ γ[A,M.X] ▷ (X ⊗ Y)) ≫ (α_ M.X X Y).inv =
      (A ◁ (α_ M.X X Y).inv) ≫ (α_ A (M.X ⊗ X) Y).inv ≫
        ((α_ A M.X X).inv ≫ γ[A,M.X] ▷ X) ▷ Y
    monoidal)
  hom_inv_id := by apply Mod_.Hom.ext; exact (α_ M.X X Y).hom_inv_id
  inv_hom_id := by apply Mod_.Hom.ext; exact (α_ M.X X Y).inv_hom_id

@[reassoc (attr := simp)]
theorem freeUnit_ambientFreeIso_hom (X Y : C) :
    (freeUnit (A := A) X ▷ Y) ≫ (ambientFreeIso X Y).hom.hom = freeUnit (X ⊗ Y) := by
  change (freeUnit X ▷ Y) ≫ (α_ A X Y).hom = freeUnit (X ⊗ Y)
  rw [← freeUnit_tensor_assoc, Iso.inv_hom_id, Category.comp_id]

/-- A twice-tensored actual free module is still free, by actual associators. -/
def ambientFreeIso₂ (X Y Z : C) :
    ambientTensor (ambientTensor (InternalModule.free A X) Y) Z ≅
      InternalModule.free A ((X ⊗ Y) ⊗ Z) :=
  ambientTensorIso (ambientFreeIso X Y) Z ≪≫ ambientFreeIso (X ⊗ Y) Z

/-- Morphisms from a twice-tensored free module are detected by its actual
generators. -/
theorem ambientFree_hom_ext₂ {X Y Z : C} {M : Mod_ C A}
    {f g : ambientTensor (ambientTensor (InternalModule.free A X) Y) Z ⟶ M}
    (h : ((freeUnit X ▷ Y) ▷ Z) ≫ f.hom = ((freeUnit X ▷ Y) ▷ Z) ≫ g.hom) : f = g := by
  apply (cancel_epi (ambientFreeIso₂ X Y Z).inv).mp
  apply free_hom_ext
  dsimp [ambientFreeIso₂, ambientTensorIso, ambientTensorMap, ambientFreeIso]
  simp only [Category.assoc]
  simp only [freeUnit_tensor_assoc, ← comp_whiskerRight_assoc, freeUnit_tensor]
  exact h

section Braided
variable [BraidedCategory C] [IsCommMonObj A]

/-- The canonical right action is an actual module morphism. -/
def rightActionHom (M : Mod_ C A) : ambientTensor M A ⟶ M :=
  Mod_.Hom.mk' (rightAction M) (by
    change ((α_ A M.X A).inv ≫ γ[A,M.X] ▷ A) ≫ rightAction M =
      (A ◁ rightAction M) ≫ γ[A,M.X]
    rw [Category.assoc, middle_assoc]
    simp)

end Braided
end Paper18.Category.RelativeTensor
