import Paper18.Category.RelativeTensorCoherence
import Paper18.Category.LocalModulesCoherence

/-! # Actual relative tensor products with free modules -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u
namespace Paper18.Category.RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C] {A : C} [MonObj A] [IsCommMonObj A]

/-- The actual module obtained by tensoring an actual module on the right
with an ambient object. -/
def ambientTensor (M : Mod_ C A) (Y : C) : Mod_ C A :=
  letI : ModObj A (M.X ⊗ Y) :=
    { smul := (α_ A M.X Y).inv ≫ γ[A,M.X] ▷ Y
      one_smul' := by
        change η[A] ▷ (M.X ⊗ Y) ≫ (α_ A M.X Y).inv ≫ γ[A,M.X] ▷ Y =
          (λ_ (M.X ⊗ Y)).hom
        calc
          _ = (α_ (𝟙_ C) M.X Y).inv ≫ (η[A] ▷ M.X ≫ γ[A,M.X]) ▷ Y := by
            monoidal
          _ = _ := by rw [InternalModule.one_smul]; monoidal
      mul_smul' := by
        change μ[A] ▷ (M.X ⊗ Y) ≫ (α_ A M.X Y).inv ≫ γ[A,M.X] ▷ Y =
          (α_ A A (M.X ⊗ Y)).hom ≫
            (A ◁ ((α_ A M.X Y).inv ≫ γ[A,M.X] ▷ Y)) ≫
              (α_ A M.X Y).inv ≫ γ[A,M.X] ▷ Y
        calc
          _ = (α_ (A ⊗ A) M.X Y).inv ≫
              (μ[A] ▷ M.X ≫ γ[A,M.X]) ▷ Y := by monoidal
          _ = (α_ (A ⊗ A) M.X Y).inv ≫
              ((α_ A A M.X).hom ≫ (A ◁ γ[A,M.X]) ≫ γ[A,M.X]) ▷ Y := by
            rw [InternalModule.mul_smul]
          _ = _ := by monoidal }
  ⟨M.X ⊗ Y⟩

/-- Contract the algebra factor in a module tensored with a free module. -/
def tensorFreeMap (M : Mod_ C A) (Y : C) :
    M.X ⊗ (InternalModule.free A Y).X ⟶ (ambientTensor M Y).X :=
  (α_ M.X A Y).inv ≫ rightAction M ▷ Y

omit [RightRigidCategory C] [HasCoequalizers C] in
theorem tensorFreeMap_balanced (M : Mod_ C A) (Y : C) :
    Balanced M (InternalModule.free A Y) (tensorFreeMap M Y) := by
  unfold Balanced parallelLeft parallelRight tensorFreeMap
  dsimp only [InternalModule.free_X]
  rw [InternalModule.free_smul]
  simp only [Category.assoc]
  change (rightAction M ▷ (A ⊗ Y)) ≫
      (α_ M.X A Y).inv ≫ rightAction M ▷ Y =
    (α_ M.X A (A ⊗ Y)).hom ≫
      (M.X ◁ ((α_ A A Y).inv ≫ μ[A] ▷ Y)) ≫
        (α_ M.X A Y).inv ≫ rightAction M ▷ Y
  calc
    _ = (α_ (M.X ⊗ A) A Y).inv ≫
        (rightAction M ▷ A ≫ rightAction M) ▷ Y := by monoidal
    _ = (α_ (M.X ⊗ A) A Y).inv ≫
        ((α_ M.X A A).hom ≫ (M.X ◁ μ[A]) ≫ rightAction M) ▷ Y := by
      have h : rightAction M ▷ A ≫ rightAction M =
          (α_ M.X A A).hom ≫ (M.X ◁ μ[A]) ≫ rightAction M := by
        rw [right_assoc]
        simp
      rw [h]
    _ = _ := by monoidal

omit [RightRigidCategory C] [HasCoequalizers C] in
theorem tensorFreeMap_linear (M : Mod_ C A) (Y : C) :
    (α_ A M.X (InternalModule.free A Y).X).inv ≫
      γ[A,M.X] ▷ (InternalModule.free A Y).X ≫ tensorFreeMap M Y =
        (A ◁ tensorFreeMap M Y) ≫ γ[A,(ambientTensor M Y).X] := by
  change (α_ A M.X (A ⊗ Y)).inv ≫ γ[A,M.X] ▷ (A ⊗ Y) ≫
      (α_ M.X A Y).inv ≫ rightAction M ▷ Y =
    (A ◁ ((α_ M.X A Y).inv ≫ rightAction M ▷ Y)) ≫
      (α_ A M.X Y).inv ≫ γ[A,M.X] ▷ Y
  calc
    _ = (α_ A M.X (A ⊗ Y)).inv ≫ (α_ (A ⊗ M.X) A Y).inv ≫
        (γ[A,M.X] ▷ A ≫ rightAction M) ▷ Y := by monoidal
    _ = (α_ A M.X (A ⊗ Y)).inv ≫ (α_ (A ⊗ M.X) A Y).inv ≫
        ((α_ A M.X A).hom ≫ (A ◁ rightAction M) ≫ γ[A,M.X]) ▷ Y := by
      rw [middle_assoc]
    _ = _ := by monoidal

/-- The balanced contraction descends to an actual module morphism. -/
def tensorFreeHom (M : Mod_ C A) (Y : C) :
    M ⊗ InternalModule.free A Y ⟶ ambientTensor M Y :=
  descModule M (InternalModule.free A Y) (ambientTensor M Y)
    (tensorFreeMap M Y) (tensorFreeMap_balanced M Y) (tensorFreeMap_linear M Y)

@[reassoc (attr := simp)]
theorem π_tensorFreeHom (M : Mod_ C A) (Y : C) :
    π M (InternalModule.free A Y) ≫ (tensorFreeHom M Y).hom = tensorFreeMap M Y :=
  π_desc _ _ _ _

/-- Insert the actual algebra unit to obtain a vector in a free module. -/
def freeUnit (Y : C) : Y ⟶ (InternalModule.free A Y).X :=
  (λ_ Y).inv ≫ η[A] ▷ Y

/-- The contraction inverse inserts the unit into the free tensor factor. -/
def tensorFreeInv (M : Mod_ C A) (Y : C) :
    ambientTensor M Y ⟶ M ⊗ InternalModule.free A Y :=
  Mod_.Hom.mk' ((M.X ◁ freeUnit Y) ≫ π M (InternalModule.free A Y)) (by
    change ((α_ A M.X Y).inv ≫ γ[A,M.X] ▷ Y) ≫
        (M.X ◁ freeUnit Y) ≫ π M (InternalModule.free A Y) =
      (A ◁ ((M.X ◁ freeUnit Y) ≫ π M (InternalModule.free A Y))) ≫
        γ[A,(tensorObj M (InternalModule.free A Y)).X]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [π_action]
    rw [associator_inv_naturality_right_assoc, ← whisker_exchange_assoc]
    rfl)

theorem tensorFreeInv_hom (M : Mod_ C A) (Y : C) :
    tensorFreeInv M Y ≫ tensorFreeHom M Y = 𝟙 _ := by
  apply Mod_.Hom.ext
  change ((M.X ◁ freeUnit Y) ≫ π M (InternalModule.free A Y)) ≫
    (tensorFreeHom M Y).hom = 𝟙 _
  rw [Category.assoc, π_tensorFreeHom]
  unfold tensorFreeMap freeUnit
  calc
    _ = ((ρ_ M.X).inv ≫ (M.X ◁ η[A]) ≫ rightAction M) ▷ Y := by monoidal
    _ = _ := by rw [rightAction_one]; simp

theorem tensorFreeHom_inv (M : Mod_ C A) (Y : C) :
    tensorFreeHom M Y ≫ tensorFreeInv M Y = 𝟙 _ := by
  apply module_hom_ext
  change π M (InternalModule.free A Y) ≫
      (tensorFreeHom M Y).hom ≫
        (M.X ◁ freeUnit Y) ≫ π M (InternalModule.free A Y) = _
  rw [π_tensorFreeHom_assoc]
  calc
    _ = (α_ M.X A Y).inv ≫ ((M.X ⊗ A) ◁ freeUnit Y) ≫
        parallelLeft M (InternalModule.free A Y) ≫ π M (InternalModule.free A Y) := by
      unfold tensorFreeMap parallelLeft
      rw [whisker_exchange_assoc]
      simp only [Category.assoc]
    _ = (α_ M.X A Y).inv ≫ ((M.X ⊗ A) ◁ freeUnit Y) ≫
        parallelRight M (InternalModule.free A Y) ≫ π M (InternalModule.free A Y) := by
      rw [condition]
    _ = _ := by
      unfold parallelRight freeUnit
      rw [InternalModule.free_smul]
      calc
        _ = (M.X ◁ ((ρ_ A).inv ≫ (A ◁ η[A]) ≫ μ[A]) ▷ Y) ≫
            π M (InternalModule.free A Y) := by monoidal
        _ = _ := by rw [MonObj.mul_one]; simp

/-- The relative tensor product with a free module is the actual ambient
tensor, with no freeness or descent conclusion assumed. -/
def tensorFreeIso (M : Mod_ C A) (Y : C) :
    M ⊗ InternalModule.free A Y ≅ ambientTensor M Y where
  hom := tensorFreeHom M Y
  inv := tensorFreeInv M Y
  hom_inv_id := tensorFreeHom_inv M Y
  inv_hom_id := tensorFreeInv_hom M Y

/-- Reassociate the actual ambient tensor of two free generators. -/
def ambientFreeIso (X Y : C) :
    ambientTensor (InternalModule.free A X) Y ≅ InternalModule.free A (X ⊗ Y) where
  hom := Mod_.Hom.mk' (α_ A X Y).hom (by
    change ((α_ A (A ⊗ X) Y).inv ≫
        ((α_ A A X).inv ≫ μ[A] ▷ X) ▷ Y) ≫ (α_ A X Y).hom =
      (A ◁ (α_ A X Y).hom) ≫ (α_ A A (X ⊗ Y)).inv ≫ μ[A] ▷ (X ⊗ Y)
    monoidal)
  inv := Mod_.Hom.mk' (α_ A X Y).inv (by
    change ((α_ A A (X ⊗ Y)).inv ≫ μ[A] ▷ (X ⊗ Y)) ≫ (α_ A X Y).inv =
      (A ◁ (α_ A X Y).inv) ≫ (α_ A (A ⊗ X) Y).inv ≫
        ((α_ A A X).inv ≫ μ[A] ▷ X) ▷ Y
    monoidal)
  hom_inv_id := by apply Mod_.Hom.ext; exact (α_ A X Y).hom_inv_id
  inv_hom_id := by apply Mod_.Hom.ext; exact (α_ A X Y).inv_hom_id

/-- The actual free tensor comparison is an isomorphism. -/
def freeTensorIso (X Y : C) :
    InternalModule.free A X ⊗ InternalModule.free A Y ≅
      InternalModule.free A (X ⊗ Y) :=
  tensorFreeIso (InternalModule.free A X) Y ≪≫ ambientFreeIso X Y

omit [BraidedCategory C] [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A] in
@[reassoc (attr := simp)]
theorem freeUnit_tensor (X Y : C) :
    freeUnit (A := A) (X ⊗ Y) ≫ (α_ A X Y).inv = freeUnit X ▷ Y := by
  unfold freeUnit
  monoidal

@[reassoc (attr := simp)]
theorem freeUnit_freeTensorIso_inv (X Y : C) :
    freeUnit (A := A) (X ⊗ Y) ≫ (freeTensorIso X Y).inv.hom =
      (freeUnit X ⊗ₘ freeUnit Y) ≫ π (InternalModule.free A X) (InternalModule.free A Y) := by
  change freeUnit (X ⊗ Y) ≫ (α_ A X Y).inv ≫
    ((A ⊗ X) ◁ freeUnit Y) ≫ π (InternalModule.free A X) (InternalModule.free A Y) = _
  rw [freeUnit_tensor_assoc]
  simp only [MonoidalCategory.tensorHom_def, InternalModule.free_X, Category.assoc]

omit [BraidedCategory C] [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A] in
theorem freeLift_freeUnit (X : C) :
    InternalModule.freeLift (freeUnit (A := A) X) = 𝟙 (InternalModule.free A X) := by
  apply Mod_.Hom.ext
  change (A ◁ ((λ_ X).inv ≫ η[A] ▷ X)) ≫
    (α_ A A X).inv ≫ μ[A] ▷ X = 𝟙 _
  calc
    _ = ((ρ_ A).inv ≫ (A ◁ η[A]) ≫ μ[A]) ▷ X := by monoidal
    _ = _ := by rw [MonObj.mul_one]; simp

omit [BraidedCategory C] [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A] in
/-- Actual module maps from a free module are determined on its generators. -/
theorem free_hom_ext {X : C} {M : Mod_ C A} {f g : InternalModule.free A X ⟶ M}
    (h : freeUnit X ≫ f.hom = freeUnit X ≫ g.hom) : f = g := by
  have hh := congrArg (fun k => InternalModule.freeLift k) h
  simpa only [← InternalModule.freeLift_comp, freeLift_freeUnit, Category.id_comp] using hh

omit [BraidedCategory C] [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A] in
@[reassoc (attr := simp)]
theorem freeUnit_naturality {X Y : C} (f : X ⟶ Y) :
    freeUnit (A := A) X ≫ (InternalModule.freeMap f).hom = f ≫ freeUnit Y := by
  change ((λ_ X).inv ≫ η[A] ▷ X) ≫ (A ◁ f) = f ≫ (λ_ Y).inv ≫ η[A] ▷ Y
  rw [Category.assoc, ← whisker_exchange, ← leftUnitor_inv_naturality_assoc]

/-- The free module on the ambient unit is the actual regular module. -/
def freeUnitIso : (𝟙_ (Mod_ C A)) ≅ InternalModule.free A (𝟙_ C) where
  hom := Mod_.Hom.mk' (ρ_ A).inv (by
    change μ[A] ≫ (ρ_ A).inv =
      (A ◁ (ρ_ A).inv) ≫ (α_ A A (𝟙_ C)).inv ≫ μ[A] ▷ (𝟙_ C)
    monoidal)
  inv := Mod_.Hom.mk' (ρ_ A).hom (by
    change ((α_ A A (𝟙_ C)).inv ≫ μ[A] ▷ (𝟙_ C)) ≫ (ρ_ A).hom =
      (A ◁ (ρ_ A).hom) ≫ μ[A]
    monoidal)
  hom_inv_id := by apply Mod_.Hom.ext; exact (ρ_ A).inv_hom_id
  inv_hom_id := by apply Mod_.Hom.ext; exact (ρ_ A).hom_inv_id

@[reassoc (attr := simp)]
theorem freeUnit_freeUnitIso_inv :
    freeUnit (A := A) (𝟙_ C) ≫ (freeUnitIso (A := A)).inv.hom = η[A] := by
  change ((λ_ (𝟙_ C)).inv ≫ η[A] ▷ (𝟙_ C)) ≫ (ρ_ A).hom = η[A]
  rw [Category.assoc, rightUnitor_naturality]
  rw [← unitors_equal, Iso.inv_hom_id_assoc]

theorem freeTensorIso_inv_natural_left {X Y : C} (f : X ⟶ Y) (Z : C) :
    (freeTensorIso (A := A) X Z).inv ≫
        InternalModule.freeMap f ▷ InternalModule.free A Z =
      InternalModule.freeMap (f ▷ Z) ≫ (freeTensorIso Y Z).inv := by
  apply free_hom_ext
  change freeUnit (X ⊗ Z) ≫ (freeTensorIso X Z).inv.hom ≫
      (InternalModule.freeMap f ▷ InternalModule.free A Z).hom =
    freeUnit (X ⊗ Z) ≫ (InternalModule.freeMap (f ▷ Z)).hom ≫
      (freeTensorIso Y Z).inv.hom
  rw [freeUnit_freeTensorIso_inv_assoc, freeUnit_naturality_assoc, π_whiskerRight]
  rw [tensorHom_comp_whiskerRight_assoc, freeUnit_naturality,
    freeUnit_freeTensorIso_inv, whiskerRight_comp_tensorHom_assoc]

theorem freeTensorIso_inv_natural_right {X Y : C} (Z : C) (f : X ⟶ Y) :
    (freeTensorIso (A := A) Z X).inv ≫
        InternalModule.free A Z ◁ InternalModule.freeMap f =
      InternalModule.freeMap (Z ◁ f) ≫ (freeTensorIso Z Y).inv := by
  apply free_hom_ext
  change freeUnit (Z ⊗ X) ≫ (freeTensorIso Z X).inv.hom ≫
      (InternalModule.free A Z ◁ InternalModule.freeMap f).hom =
    freeUnit (Z ⊗ X) ≫ (InternalModule.freeMap (Z ◁ f)).hom ≫
      (freeTensorIso Z Y).inv.hom
  rw [freeUnit_freeTensorIso_inv_assoc, freeUnit_naturality_assoc, π_whiskerLeft]
  rw [tensorHom_comp_whiskerLeft_assoc, freeUnit_naturality,
    freeUnit_freeTensorIso_inv, whiskerLeft_comp_tensorHom_assoc]

theorem freeTensorIso_inv_associativity (X Y Z : C) :
    (freeTensorIso (A := A) (X ⊗ Y) Z).inv ≫
        (freeTensorIso X Y).inv ▷ InternalModule.free A Z ≫
          (α_ (InternalModule.free A X) (InternalModule.free A Y)
            (InternalModule.free A Z)).hom =
      InternalModule.freeMap (α_ X Y Z).hom ≫ (freeTensorIso X (Y ⊗ Z)).inv ≫
        InternalModule.free A X ◁ (freeTensorIso Y Z).inv := by
  apply free_hom_ext
  change freeUnit ((X ⊗ Y) ⊗ Z) ≫ (freeTensorIso (X ⊗ Y) Z).inv.hom ≫
      ((freeTensorIso X Y).inv ▷ InternalModule.free A Z).hom ≫
        (α_ (InternalModule.free A X) (InternalModule.free A Y)
          (InternalModule.free A Z)).hom.hom =
    freeUnit ((X ⊗ Y) ⊗ Z) ≫ (InternalModule.freeMap (α_ X Y Z).hom).hom ≫
      (freeTensorIso X (Y ⊗ Z)).inv.hom ≫
        (InternalModule.free A X ◁ (freeTensorIso Y Z).inv).hom
  rw [freeUnit_freeTensorIso_inv_assoc, freeUnit_naturality_assoc,
    π_whiskerRight_assoc, tensorHom_comp_whiskerRight_assoc,
    freeUnit_freeTensorIso_inv, freeUnit_freeTensorIso_inv_assoc,
    π_whiskerLeft, tensorHom_comp_whiskerLeft_assoc, freeUnit_freeTensorIso_inv]
  rw [← tensorHom_comp_whiskerRight_assoc, π_associator,
    ← tensorHom_comp_whiskerLeft_assoc, associator_naturality_assoc]

theorem freeTensorIso_inv_left_unitality (X : C) :
    (freeTensorIso (A := A) (𝟙_ C) X).inv ≫
        (freeUnitIso (A := A)).inv ▷ InternalModule.free A X ≫
          (λ_ (InternalModule.free A X)).hom =
      InternalModule.freeMap (λ_ X).hom := by
  apply free_hom_ext
  change freeUnit ((𝟙_ C) ⊗ X) ≫ (freeTensorIso (𝟙_ C) X).inv.hom ≫
      ((freeUnitIso (A := A)).inv ▷ InternalModule.free A X).hom ≫
        (λ_ (InternalModule.free A X)).hom.hom =
    freeUnit ((𝟙_ C) ⊗ X) ≫ (InternalModule.freeMap (λ_ X).hom).hom
  rw [freeUnit_freeTensorIso_inv_assoc, π_whiskerRight_assoc,
    tensorHom_comp_whiskerRight_assoc, freeUnit_freeUnitIso_inv,
    π_leftUnitor, freeUnit_naturality]
  rw [MonoidalCategory.tensorHom_def', Category.assoc,
    InternalModule.one_smul (InternalModule.free A X)]
  exact leftUnitor_naturality _

theorem freeTensorIso_inv_right_unitality (X : C) :
    (freeTensorIso (A := A) X (𝟙_ C)).inv ≫
        InternalModule.free A X ◁ (freeUnitIso (A := A)).inv ≫
          (ρ_ (InternalModule.free A X)).hom =
      InternalModule.freeMap (ρ_ X).hom := by
  apply free_hom_ext
  change freeUnit (X ⊗ (𝟙_ C)) ≫ (freeTensorIso X (𝟙_ C)).inv.hom ≫
      (InternalModule.free A X ◁ (freeUnitIso (A := A)).inv).hom ≫
        (ρ_ (InternalModule.free A X)).hom.hom =
    freeUnit (X ⊗ (𝟙_ C)) ≫ (InternalModule.freeMap (ρ_ X).hom).hom
  rw [freeUnit_freeTensorIso_inv_assoc, π_whiskerLeft_assoc,
    tensorHom_comp_whiskerLeft_assoc, freeUnit_freeUnitIso_inv,
    π_rightUnitor, freeUnit_naturality]
  rw [MonoidalCategory.tensorHom_def, Category.assoc, rightAction_one]
  exact rightUnitor_naturality _

/-- The checked inverse tensor comparisons give the actual free functor
an oplax monoidal structure. -/
instance freeFunctorOplaxMonoidal :
    (InternalModule.freeFunctor (A := A)).OplaxMonoidal where
  «η» := (freeUnitIso (A := A)).inv
  δ X Y := (freeTensorIso X Y).inv
  δ_natural_left f Z := freeTensorIso_inv_natural_left f Z
  δ_natural_right Z f := freeTensorIso_inv_natural_right Z f
  oplax_associativity := freeTensorIso_inv_associativity
  oplax_left_unitality X := by
    apply (cancel_mono (λ_ (InternalModule.free A X)).hom).mp
    change (λ_ (InternalModule.free A X)).inv ≫ (λ_ (InternalModule.free A X)).hom =
      (InternalModule.freeMap (λ_ X).inv ≫ (freeTensorIso (𝟙_ C) X).inv ≫
        (freeUnitIso (A := A)).inv ▷ InternalModule.free A X) ≫
          (λ_ (InternalModule.free A X)).hom
    rw [Iso.inv_hom_id]
    simp only [Category.assoc]
    rw [freeTensorIso_inv_left_unitality]
    apply Mod_.Hom.ext
    change 𝟙 _ = (A ◁ (λ_ X).inv) ≫ (A ◁ (λ_ X).hom)
    rw [← whiskerLeft_comp, Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id]
  oplax_right_unitality X := by
    apply (cancel_mono (ρ_ (InternalModule.free A X)).hom).mp
    change (ρ_ (InternalModule.free A X)).inv ≫ (ρ_ (InternalModule.free A X)).hom =
      (InternalModule.freeMap (ρ_ X).inv ≫ (freeTensorIso X (𝟙_ C)).inv ≫
        InternalModule.free A X ◁ (freeUnitIso (A := A)).inv) ≫
          (ρ_ (InternalModule.free A X)).hom
    rw [Iso.inv_hom_id]
    simp only [Category.assoc]
    rw [freeTensorIso_inv_right_unitality]
    apply Mod_.Hom.ext
    change 𝟙 _ = (A ◁ (ρ_ X).inv) ≫ (A ◁ (ρ_ X).hom)
    rw [← whiskerLeft_comp, Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id]

instance freeFunctorOplaxUnitIsIso :
    IsIso (Functor.OplaxMonoidal.η (InternalModule.freeFunctor (A := A))) := by
  change IsIso (freeUnitIso (A := A)).inv
  infer_instance

instance freeFunctorOplaxTensorIsIso (X Y : C) :
    IsIso (Functor.OplaxMonoidal.δ (InternalModule.freeFunctor (A := A)) X Y) := by
  change IsIso (freeTensorIso (A := A) X Y).inv
  infer_instance

/-- The actual free module functor is strong monoidal: both its tensor
comparison and its unit comparison are actual proved isomorphisms. -/
instance freeFunctorMonoidal : (InternalModule.freeFunctor (A := A)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    (Functor.CoreMonoidal.ofOplaxMonoidal (InternalModule.freeFunctor (A := A)))

@[simp]
theorem freeFunctor_μ_eq (X Y : C) :
    Functor.LaxMonoidal.μ (InternalModule.freeFunctor (A := A)) X Y =
      (freeTensorIso X Y).hom := by
  apply (cancel_epi (freeTensorIso (A := A) X Y).inv).mp
  change Functor.OplaxMonoidal.δ (InternalModule.freeFunctor (A := A)) X Y ≫
      Functor.LaxMonoidal.μ (InternalModule.freeFunctor (A := A)) X Y =
    (freeTensorIso X Y).inv ≫ (freeTensorIso X Y).hom
  rw [Functor.Monoidal.δ_μ, Iso.inv_hom_id]
  rfl

@[simp]
theorem freeFunctor_ε_eq :
    Functor.LaxMonoidal.ε (InternalModule.freeFunctor (A := A)) =
      (freeUnitIso (A := A)).hom := by
  apply (cancel_epi (freeUnitIso (A := A)).inv).mp
  change Functor.OplaxMonoidal.η (InternalModule.freeFunctor (A := A)) ≫
      Functor.LaxMonoidal.ε (InternalModule.freeFunctor (A := A)) =
    (freeUnitIso (A := A)).inv ≫ (freeUnitIso (A := A)).hom
  rw [Functor.Monoidal.η_ε, Iso.inv_hom_id]
  rfl

@[reassoc]
theorem freeTensorIso_inv_braiding (hA : A ∈ mugerCenter (C := C)) (X Y : C) :
    letI := moduleBraidedOfTransparent hA
    (freeTensorIso (A := A) X Y).inv ≫
        (β_ (InternalModule.free A X) (InternalModule.free A Y)).hom =
      InternalModule.freeMap (β_ X Y).hom ≫ (freeTensorIso Y X).inv := by
  letI := moduleBraidedOfTransparent hA
  apply free_hom_ext
  change freeUnit (X ⊗ Y) ≫ (freeTensorIso X Y).inv.hom ≫
      (β_ (InternalModule.free A X) (InternalModule.free A Y)).hom.hom =
    freeUnit (X ⊗ Y) ≫ (InternalModule.freeMap (β_ X Y).hom).hom ≫
      (freeTensorIso Y X).inv.hom
  rw [freeUnit_freeTensorIso_inv_assoc, π_moduleBraidingOfTransparent,
    freeUnit_naturality_assoc, freeUnit_freeTensorIso_inv]
  exact BraidedCategory.braiding_naturality_assoc _ _ _

/-- For a transparent algebra, the actual strong free functor preserves
the actual descended braiding. -/
def freeFunctorBraidedOfTransparent (hA : A ∈ mugerCenter (C := C)) :
    letI := moduleBraidedOfTransparent hA
    (InternalModule.freeFunctor (A := A)).Braided := by
  letI := moduleBraidedOfTransparent hA
  exact
    { toMonoidal := freeFunctorMonoidal
      braided X Y := by
        apply (cancel_epi (freeTensorIso (A := A) X Y).inv).mp
        change (freeTensorIso X Y).inv ≫
            Functor.LaxMonoidal.μ (InternalModule.freeFunctor (A := A)) X Y ≫
              InternalModule.freeMap (β_ X Y).hom =
          (freeTensorIso X Y).inv ≫
            (β_ (InternalModule.free A X) (InternalModule.free A Y)).hom ≫
              Functor.LaxMonoidal.μ (InternalModule.freeFunctor (A := A)) Y X
        rw [freeTensorIso_inv_braiding_assoc hA]
        change Functor.OplaxMonoidal.δ (InternalModule.freeFunctor (A := A)) X Y ≫
            Functor.LaxMonoidal.μ (InternalModule.freeFunctor (A := A)) X Y ≫
              InternalModule.freeMap (β_ X Y).hom =
          InternalModule.freeMap (β_ X Y).hom ≫
            Functor.OplaxMonoidal.δ (InternalModule.freeFunctor (A := A)) Y X ≫
              Functor.LaxMonoidal.μ (InternalModule.freeFunctor (A := A)) Y X
        simp only [Functor.Monoidal.δ_μ_assoc, Functor.Monoidal.δ_μ]
        erw [Category.comp_id] }

section Linear
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The actual free-module universal property, including its complex-linear
structure on Hom spaces. -/
def freeHomLinearEquiv (X : C) (M : Mod_ C A) :
    (InternalModule.free A X ⟶ M) ≃ₗ[ℂ] (X ⟶ M.X) where
  toFun f := freeUnit X ≫ f.hom
  invFun := InternalModule.freeLift
  left_inv f := by
    apply free_hom_ext
    simpa only [freeUnit, Category.assoc] using
      (InternalModule.unit_freeLift (freeUnit X ≫ f.hom))
  right_inv f := by
    simpa only [freeUnit, Category.assoc] using InternalModule.unit_freeLift f
  map_add' f g := by simp only [InternalModule.add_hom, Preadditive.comp_add]
  map_smul' c f := by simp only [InternalModule.smul_hom, Linear.comp_smul, RingHom.id_apply]

/-- The endomorphisms of the actual monoidal unit of relative modules are
the ambient maps from the unit into the actual algebra. -/
def unitEndLinearEquiv :
    ((𝟙_ (Mod_ C A)) ⟶ (𝟙_ (Mod_ C A))) ≃ₗ[ℂ] ((𝟙_ C) ⟶ A) :=
  (CategoryTheory.Linear.homCongr ℂ (freeUnitIso (A := A)) (Iso.refl _)).trans
    (freeHomLinearEquiv (𝟙_ C) (𝟙_ (Mod_ C A)))

end Linear

end Paper18.Category.RelativeTensor
