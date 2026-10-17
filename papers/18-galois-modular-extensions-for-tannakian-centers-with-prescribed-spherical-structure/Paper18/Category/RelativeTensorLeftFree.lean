import Paper18.Category.RelativeTensorAmbient

/-! # Actual left-free relative tensor comparisons -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory
open scoped MonObj
universe v u
namespace Paper18.Category.RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {A : C} [MonObj A] [IsCommMonObj A]

/-- The ambient contraction is a composite of actual module morphisms. -/
def leftFreeLinearHom (X : C) (M : Mod_ C A) :
    ambientTensor (InternalModule.free A X) M.X ⟶ ambientTensor M X :=
  (ambientFreeIso X M.X).hom ≫ InternalModule.freeLift (β_ X M.X).hom

omit [IsCommMonObj A] in
@[reassoc]
theorem leftFreeLinearHom_hom (X : C) (M : Mod_ C A) :
    (leftFreeLinearHom X M).hom =
      (α_ A X M.X).hom ≫ (A ◁ (β_ X M.X).hom) ≫
        (α_ A M.X X).inv ≫ γ[A,M.X] ▷ X := rfl

omit [IsCommMonObj A] in
@[reassoc (attr := simp)]
theorem freeUnit_leftFreeLinearHom (X : C) (M : Mod_ C A) :
    (freeUnit X ▷ M.X) ≫ (leftFreeLinearHom X M).hom = (β_ X M.X).hom := by
  change (freeUnit X ▷ M.X) ≫ (ambientFreeIso X M.X).hom.hom ≫
    (InternalModule.freeLift (M := ambientTensor M X) (β_ X M.X).hom).hom = _
  rw [freeUnit_ambientFreeIso_hom_assoc]
  simpa only [freeUnit, Category.assoc] using
    InternalModule.unit_freeLift (M := ambientTensor M X) (β_ X M.X).hom

omit [IsCommMonObj A] in
@[reassoc (attr := simp)]
theorem freeUnit_rightAction (X : C) :
    (freeUnit X ▷ A) ≫ rightAction (InternalModule.free A X) = (β_ X A).hom := by
  have hu : (A ◁ freeUnit (A := A) X) ≫ γ[A,(InternalModule.free A X).X] = 𝟙 _ :=
    congrArg Mod_.Hom.hom (freeLift_freeUnit (A := A) X)
  unfold rightAction
  rw [braiding_naturality_left_assoc, hu]
  erw [Category.comp_id]

omit [IsCommMonObj A] in
/-- The ambient contraction intertwines the crossed algebra action by the
actual braiding hexagon and naturality. -/
@[reassoc]
theorem leftFreeLinearHom_braid_action (X : C) (M : Mod_ C A) :
    (β_ X A).hom ▷ M.X ≫ (leftFreeLinearHom X M).hom =
      (α_ X A M.X).hom ≫ (X ◁ γ[A,M.X]) ≫ (β_ X M.X).hom := by
  rw [braiding_naturality_right, braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, leftFreeLinearHom_hom]

/-- The contraction is balanced, proved on actual free generators of the
raw module tensor, then using the crossed algebra-action equation. -/
theorem leftFreeLinearHom_balanced (X : C) (M : Mod_ C A) :
    Balanced (InternalModule.free A X) M (leftFreeLinearHom X M).hom := by
  let L := ambientTensorMap (rightActionHom (InternalModule.free A X)) M.X ≫ leftFreeLinearHom X M
  let R := (ambientTensorAssoc (InternalModule.free A X) A M.X).hom ≫
    ambientTensorMapRight (InternalModule.free A X) γ[A,M.X] ≫ leftFreeLinearHom X M
  have h : L = R := by
    apply ambientFree_hom_ext₂
    change ((freeUnit X ▷ A) ▷ M.X) ≫ rightAction (InternalModule.free A X) ▷ M.X ≫
        (leftFreeLinearHom X M).hom =
      ((freeUnit X ▷ A) ▷ M.X) ≫ (α_ (InternalModule.free A X).X A M.X).hom ≫
        ((InternalModule.free A X).X ◁ γ[A,M.X]) ≫ (leftFreeLinearHom X M).hom
    rw [← comp_whiskerRight_assoc, freeUnit_rightAction,
      associator_naturality_left_assoc, ← whisker_exchange_assoc,
      freeUnit_leftFreeLinearHom]
    exact leftFreeLinearHom_braid_action X M
  have hh := congrArg Mod_.Hom.hom h
  change rightAction (InternalModule.free A X) ▷ M.X ≫ (leftFreeLinearHom X M).hom =
    (α_ (InternalModule.free A X).X A M.X).hom ≫
      ((InternalModule.free A X).X ◁ γ[A,M.X]) ≫ (leftFreeLinearHom X M).hom at hh
  simpa only [Balanced, parallelLeft, parallelRight, Category.assoc] using hh

section Quotient
variable [RightRigidCategory C] [HasCoequalizers C]

/-- The balanced contraction descends to an actual module morphism. -/
def leftFreeHom (X : C) (M : Mod_ C A) :
    InternalModule.free A X ⊗ M ⟶ ambientTensor M X :=
  descModule _ _ _ (leftFreeLinearHom X M).hom (leftFreeLinearHom_balanced X M)
    (by
      have h := IsMod_Hom.smul_hom (A := A) (f := (leftFreeLinearHom X M).hom)
      change ((α_ A (InternalModule.free A X).X M.X).inv ≫
        γ[A,(InternalModule.free A X).X] ▷ M.X) ≫ (leftFreeLinearHom X M).hom =
        (A ◁ (leftFreeLinearHom X M).hom) ≫ γ[A,(ambientTensor M X).X] at h
      simpa only [Category.assoc] using h)

@[reassoc (attr := simp)]
theorem π_leftFreeHom (X : C) (M : Mod_ C A) :
    π (InternalModule.free A X) M ≫ (leftFreeHom X M).hom = (leftFreeLinearHom X M).hom :=
  π_desc _ _ _ _

/-- The balancing equation evaluated on the actual free generators. -/
@[reassoc]
theorem π_leftFree_generators (X : C) (M : Mod_ C A) :
    (β_ X A).hom ▷ M.X ≫ π (InternalModule.free A X) M =
      (α_ X A M.X).hom ≫ (X ◁ γ[A,M.X]) ≫
        (freeUnit X ▷ M.X) ≫ π (InternalModule.free A X) M := by
  have h := congrArg (fun k => ((freeUnit X ▷ A) ▷ M.X) ≫ k)
    (condition (InternalModule.free A X) M)
  dsimp only [parallelLeft, parallelRight] at h
  simp only [Category.assoc] at h
  change ((freeUnit X ▷ A) ▷ M.X) ≫ rightAction (InternalModule.free A X) ▷ M.X ≫
      π (InternalModule.free A X) M =
    ((freeUnit X ▷ A) ▷ M.X) ≫ (α_ (InternalModule.free A X).X A M.X).hom ≫
      ((InternalModule.free A X).X ◁ γ[A,M.X]) ≫ π (InternalModule.free A X) M at h
  rw [← comp_whiskerRight_assoc, freeUnit_rightAction,
    associator_naturality_left_assoc, ← whisker_exchange_assoc] at h
  exact h

/-- The inverse comparison inserts the actual algebra unit after moving
the free generator past the actual module. -/
def leftFreeInvUnderlying (X : C) (M : Mod_ C A) :
    (ambientTensor M X).X ⟶ (InternalModule.free A X ⊗ M).X :=
  (β_ X M.X).inv ≫ (freeUnit X ▷ M.X) ≫ π (InternalModule.free A X) M

@[reassoc]
theorem leftFreeInvUnderlying_hom (X : C) (M : Mod_ C A) :
    leftFreeInvUnderlying X M ≫ (leftFreeHom X M).hom = 𝟙 _ := by
  unfold leftFreeInvUnderlying
  rw [Category.assoc, Category.assoc, π_leftFreeHom, freeUnit_leftFreeLinearHom]
  exact (β_ X M.X).inv_hom_id

@[reassoc]
theorem leftFreeHom_invUnderlying (X : C) (M : Mod_ C A) :
    (leftFreeHom X M).hom ≫ leftFreeInvUnderlying X M = 𝟙 _ := by
  apply hom_ext (InternalModule.free A X) M
  rw [π_leftFreeHom_assoc]
  unfold leftFreeInvUnderlying
  apply (cancel_epi ((β_ X A).hom ▷ M.X)).mp
  rw [leftFreeLinearHom_braid_action_assoc, Iso.hom_inv_id_assoc, π_leftFree_generators_assoc]
  erw [Category.comp_id]

/-- The actual relative tensor with a free left factor is an actual
ambient tensor, proved from the balancing coequalizer and the free unit. -/
def leftFreeIso (X : C) (M : Mod_ C A) :
    InternalModule.free A X ⊗ M ≅ ambientTensor M X := by
  let z : (InternalModule.free A X ⊗ M).X ≅ (ambientTensor M X).X :=
    { hom := (leftFreeHom X M).hom
      inv := leftFreeInvUnderlying X M
      hom_inv_id := leftFreeHom_invUnderlying X M
      inv_hom_id := leftFreeInvUnderlying_hom X M }
  letI : IsIso (leftFreeHom X M).hom := z.isIso_hom
  letI : IsMod_Hom A (asIso (leftFreeHom X M).hom).hom := (leftFreeHom X M).isMod_Hom
  let h : ambientTensor M X ⟶ InternalModule.free A X ⊗ M :=
    ⟨(asIso (leftFreeHom X M).hom).inv⟩
  exact
    { hom := leftFreeHom X M
      inv := h
      hom_inv_id := by apply Mod_.Hom.ext; exact IsIso.hom_inv_id (leftFreeHom X M).hom
      inv_hom_id := by apply Mod_.Hom.ext; exact IsIso.inv_hom_id (leftFreeHom X M).hom }

/-- The actual free module commutes with every actual module. -/
def freeCentralIso (X : C) (M : Mod_ C A) :
    InternalModule.free A X ⊗ M ≅ M ⊗ InternalModule.free A X :=
  leftFreeIso X M ≪≫ (tensorFreeIso M X).symm

end Quotient
end Paper18.Category.RelativeTensor
