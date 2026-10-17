import Paper18.Category.RelativeTensorCentralFree

/-! # Actual centrality of the free tensor and unit comparisons -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory
open scoped MonObj
universe v u
namespace Paper18.Category.RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C] {A : C} [MonObj A] [IsCommMonObj A]

/-- The inverse unit comparison intertwines the actual free half-braiding
with the canonical unit half-braiding. -/
theorem freeUnitIso_inv_central (M : Mod_ C A) :
    (freeUnitIso (A := A)).inv ▷ M ≫ (λ_ M).hom =
      (freeCentralIso (𝟙_ C) M).hom ≫ M ◁ (freeUnitIso (A := A)).inv ≫ (ρ_ M).hom := by
  apply freeCentral_hom_ext
  simp only [freeTensorGenerator, Mod_.comp_hom', Category.assoc]
  rw [π_whiskerRight_assoc, ← comp_whiskerRight_assoc, freeUnit_freeUnitIso_inv,
    π_leftUnitor, freeUnit_π_freeCentralIso_assoc, π_whiskerLeft_assoc,
    ← whiskerLeft_comp_assoc, freeUnit_freeUnitIso_inv, π_rightUnitor,
    rightAction_one M, InternalModule.one_smul M]
  rw [braiding_tensorUnit_left]
  simp

/-- The actual unit comparison as a morphism in the actual Drinfeld center. -/
def centralFreeUnitInv : (centralFreeFunctor (A := A)).obj (𝟙_ C) ⟶ 𝟙_ (Center (Mod_ C A)) where
  f := (freeUnitIso (A := A)).inv
  comm M := by
    apply (cancel_mono (ρ_ M).hom).mp
    simp only [Center.tensorUnit_β, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    change (freeUnitIso (A := A)).inv ▷ M ≫ (λ_ M).hom ≫ (ρ_ M).inv ≫ (ρ_ M).hom =
      (freeCentralIso (𝟙_ C) M).hom ≫ M ◁ (freeUnitIso (A := A)).inv ≫ (ρ_ M).hom
    rw [Iso.inv_hom_id, Category.comp_id]
    exact freeUnitIso_inv_central M

private def twoFreeGenerator (X Y : C) (M : Mod_ C A) :
    (X ⊗ Y) ⊗ M.X ⟶ ((InternalModule.free A X ⊗ InternalModule.free A Y) ⊗ M).X :=
  ((freeUnit X ⊗ₘ freeUnit Y) ▷ M.X) ≫
    (π (InternalModule.free A X) (InternalModule.free A Y) ▷ M.X) ≫
      π (InternalModule.free A X ⊗ InternalModule.free A Y) M

@[reassoc]
private theorem twoFreeGenerator_first (X Y : C) (M : Mod_ C A) :
    twoFreeGenerator X Y M ≫ (α_ (InternalModule.free A X) (InternalModule.free A Y) M).hom.hom ≫
        (InternalModule.free A X ◁ (freeCentralIso Y M).hom).hom =
      (α_ X Y M.X).hom ≫
        (X ◁ ((freeUnit Y ▷ M.X) ≫ π (InternalModule.free A Y) M ≫ (freeCentralIso Y M).hom.hom)) ≫
        (freeUnit X ▷ (M ⊗ InternalModule.free A Y).X) ≫
        π (InternalModule.free A X) (M ⊗ InternalModule.free A Y) := by
  unfold twoFreeGenerator
  simp only [Category.assoc]
  rw [π_associator_assoc, π_whiskerLeft]
  simp only [MonoidalCategory.tensorHom_def', comp_whiskerRight, Category.assoc]
  rw [associator_naturality_left_assoc, associator_naturality_middle_assoc]
  erw [← whisker_exchange_assoc, ← whisker_exchange_assoc]
  simp only [whiskerLeft_comp, Category.assoc]

@[reassoc]
private theorem twoFreeGenerator_second (X Y : C) (M : Mod_ C A) :
    (X ◁ ((M.X ◁ freeUnit Y) ≫ π M (InternalModule.free A Y))) ≫
        (freeUnit X ▷ (M ⊗ InternalModule.free A Y).X) ≫
        π (InternalModule.free A X) (M ⊗ InternalModule.free A Y) ≫
        (α_ (InternalModule.free A X) M (InternalModule.free A Y)).inv.hom ≫
        ((freeCentralIso X M).hom ▷ InternalModule.free A Y).hom =
      (α_ X M.X Y).inv ≫
        (((freeUnit X ▷ M.X) ≫ π (InternalModule.free A X) M ≫ (freeCentralIso X M).hom.hom) ▷ Y) ≫
        ((M ⊗ InternalModule.free A X).X ◁ freeUnit Y) ≫
        π (M ⊗ InternalModule.free A X) (InternalModule.free A Y) := by
  erw [whisker_exchange_assoc]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [π_associator_inv_assoc, π_whiskerRight]
  erw [associator_inv_naturality_right_assoc, associator_inv_naturality_left_assoc]
  erw [whisker_exchange_assoc, whisker_exchange_assoc]
  simp only [comp_whiskerRight, Category.assoc]

@[reassoc]
private theorem twoFreeGenerator_third (X Y : C) (M : Mod_ C A) :
    ((M.X ◁ freeUnit X) ▷ Y) ≫ (π M (InternalModule.free A X) ▷ Y) ≫
        ((M ⊗ InternalModule.free A X).X ◁ freeUnit Y) ≫
        π (M ⊗ InternalModule.free A X) (InternalModule.free A Y) ≫
        (α_ M (InternalModule.free A X) (InternalModule.free A Y)).hom.hom =
      (α_ M.X X Y).hom ≫ (M.X ◁ (freeUnit X ⊗ₘ freeUnit Y)) ≫
        (M.X ◁ π (InternalModule.free A X) (InternalModule.free A Y)) ≫
        π M (InternalModule.free A X ⊗ InternalModule.free A Y) := by
  erw [← whisker_exchange_assoc, π_associator]
  simp only [MonoidalCategory.tensorHom_def, whiskerLeft_comp, Category.assoc]
  monoidal

@[reassoc]
private theorem twoFreeGenerator_tensorHalf (X Y : C) (M : Mod_ C A) :
    twoFreeGenerator X Y M ≫ (α_ (InternalModule.free A X) (InternalModule.free A Y) M).hom.hom ≫
        (InternalModule.free A X ◁ (freeCentralIso Y M).hom).hom ≫
        (α_ (InternalModule.free A X) M (InternalModule.free A Y)).inv.hom ≫
        ((freeCentralIso X M).hom ▷ InternalModule.free A Y).hom ≫
        (α_ M (InternalModule.free A X) (InternalModule.free A Y)).hom.hom =
      (β_ (X ⊗ Y) M.X).hom ≫ (M.X ◁ (freeUnit X ⊗ₘ freeUnit Y)) ≫
        (M.X ◁ π (InternalModule.free A X) (InternalModule.free A Y)) ≫
        π M (InternalModule.free A X ⊗ InternalModule.free A Y) := by
  rw [twoFreeGenerator_first_assoc, freeUnit_π_freeCentralIso]
  rw [whiskerLeft_comp, Category.assoc, twoFreeGenerator_second_assoc,
    freeUnit_π_freeCentralIso]
  simp only [comp_whiskerRight, Category.assoc]
  rw [twoFreeGenerator_third, braiding_tensor_left_hom]
  simp only [Category.assoc]

/-- The inverse tensor comparison intertwines the actual free half-braiding
with the actual tensor product of half-braidings. -/
theorem freeTensorIso_inv_central (X Y : C) (M : Mod_ C A) :
    (freeTensorIso (A := A) X Y).inv ▷ M ≫
        ((centralFreeObj X ⊗ centralFreeObj Y).snd.β M).hom =
      (freeCentralIso (X ⊗ Y) M).hom ≫ M ◁ (freeTensorIso X Y).inv := by
  apply freeCentral_hom_ext
  simp only [freeTensorGenerator, Mod_.comp_hom', Category.assoc]
  rw [π_whiskerRight_assoc, ← comp_whiskerRight_assoc, freeUnit_freeTensorIso_inv,
    freeUnit_π_freeCentralIso_assoc, π_whiskerLeft, ← whiskerLeft_comp_assoc,
    freeUnit_freeTensorIso_inv]
  change (((freeUnit X ⊗ₘ freeUnit Y) ≫ π (InternalModule.free A X) (InternalModule.free A Y)) ▷ M.X) ≫
      π (InternalModule.free A X ⊗ InternalModule.free A Y) M ≫
      (α_ (InternalModule.free A X) (InternalModule.free A Y) M).hom.hom ≫
      (InternalModule.free A X ◁ (freeCentralIso Y M).hom).hom ≫
      (α_ (InternalModule.free A X) M (InternalModule.free A Y)).inv.hom ≫
      ((freeCentralIso X M).hom ▷ InternalModule.free A Y).hom ≫
      (α_ M (InternalModule.free A X) (InternalModule.free A Y)).hom.hom =
    (β_ (X ⊗ Y) M.X).hom ≫
      (M.X ◁ ((freeUnit X ⊗ₘ freeUnit Y) ≫ π (InternalModule.free A X) (InternalModule.free A Y))) ≫
      π M (InternalModule.free A X ⊗ InternalModule.free A Y)
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  simpa only [twoFreeGenerator, Category.assoc] using twoFreeGenerator_tensorHalf X Y M

/-- The actual tensor comparison as a morphism in the actual Drinfeld center. -/
def centralFreeTensorInv (X Y : C) :
    (centralFreeFunctor (A := A)).obj (X ⊗ Y) ⟶
      (centralFreeFunctor (A := A)).obj X ⊗ (centralFreeFunctor (A := A)).obj Y where
  f := (freeTensorIso X Y).inv
  comm M := freeTensorIso_inv_central X Y M

/-- The actual central free half-braiding agrees with the ambient braiding
on the two actual free generators. -/
@[reassoc]
theorem freeTensorIso_inv_centralBraiding (X Y : C) :
    (freeTensorIso (A := A) X Y).inv ≫ (freeCentralIso X (InternalModule.free A Y)).hom =
      InternalModule.freeMap (β_ X Y).hom ≫ (freeTensorIso Y X).inv := by
  apply free_hom_ext
  change freeUnit (X ⊗ Y) ≫ (freeTensorIso X Y).inv.hom ≫
      (freeCentralIso X (InternalModule.free A Y)).hom.hom =
    freeUnit (X ⊗ Y) ≫ (InternalModule.freeMap (β_ X Y).hom).hom ≫ (freeTensorIso Y X).inv.hom
  rw [freeUnit_freeTensorIso_inv_assoc, freeUnit_naturality_assoc, freeUnit_freeTensorIso_inv]
  rw [MonoidalCategory.tensorHom_def', Category.assoc, freeUnit_π_freeCentralIso]
  rw [braiding_naturality_right_assoc]
  simp only [MonoidalCategory.tensorHom_def, Category.assoc]

/-- The actual inverse free comparisons give the actual central lift an
oplax monoidal structure. -/
instance centralFreeFunctorOplaxMonoidal : (centralFreeFunctor (A := A)).OplaxMonoidal where
  «η» := centralFreeUnitInv
  δ := centralFreeTensorInv
  δ_natural_left f Z := by
    apply Center.ext
    exact freeTensorIso_inv_natural_left f Z
  δ_natural_right Z f := by
    apply Center.ext
    exact freeTensorIso_inv_natural_right Z f
  oplax_associativity X Y Z := by
    apply Center.ext
    exact freeTensorIso_inv_associativity X Y Z
  oplax_left_unitality X := by
    apply Center.ext
    simp only [Center.leftUnitor_inv_f, Center.comp_f, Center.whiskerRight_f]
    change (λ_ (InternalModule.free A X)).inv =
      InternalModule.freeMap (λ_ X).inv ≫ (freeTensorIso (𝟙_ C) X).inv ≫
        (freeUnitIso (A := A)).inv ▷ InternalModule.free A X
    exact (freeFunctorOplaxMonoidal (A := A)).oplax_left_unitality X
  oplax_right_unitality X := by
    apply Center.ext
    simp only [Center.rightUnitor_inv_f, Center.comp_f, Center.whiskerLeft_f]
    change (ρ_ (InternalModule.free A X)).inv =
      InternalModule.freeMap (ρ_ X).inv ≫ (freeTensorIso X (𝟙_ C)).inv ≫
        InternalModule.free A X ◁ (freeUnitIso (A := A)).inv
    exact (freeFunctorOplaxMonoidal (A := A)).oplax_right_unitality X

instance centralFreeFunctorOplaxUnitIsIso :
    IsIso (Functor.OplaxMonoidal.η (centralFreeFunctor (A := A))) := by
  change IsIso (centralFreeUnitInv (A := A))
  letI : IsIso (centralFreeUnitInv (A := A)).f :=
    show IsIso (freeUnitIso (A := A)).inv from inferInstance
  exact Center.isIso_of_f_isIso _

instance centralFreeFunctorOplaxTensorIsIso (X Y : C) :
    IsIso (Functor.OplaxMonoidal.δ (centralFreeFunctor (A := A)) X Y) := by
  change IsIso (centralFreeTensorInv (A := A) X Y)
  letI : IsIso (centralFreeTensorInv (A := A) X Y).f :=
    show IsIso (freeTensorIso (A := A) X Y).inv from inferInstance
  exact Center.isIso_of_f_isIso _

/-- The actual free module functor lifts to an actual strong monoidal
functor into the actual Drinfeld center. -/
instance centralFreeFunctorMonoidal : (centralFreeFunctor (A := A)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    (Functor.CoreMonoidal.ofOplaxMonoidal (centralFreeFunctor (A := A)))

@[reassoc]
theorem centralFreeFunctor_δ_braiding (X Y : C) :
    Functor.OplaxMonoidal.δ (centralFreeFunctor (A := A)) X Y ≫
        (β_ ((centralFreeFunctor (A := A)).obj X) ((centralFreeFunctor (A := A)).obj Y)).hom =
      (centralFreeFunctor (A := A)).map (β_ X Y).hom ≫
        Functor.OplaxMonoidal.δ (centralFreeFunctor (A := A)) Y X := by
  apply Center.ext
  exact freeTensorIso_inv_centralBraiding X Y

/-- The actual central lift preserves the actual ambient braiding. -/
instance centralFreeFunctorBraided : (centralFreeFunctor (A := A)).Braided where
  toMonoidal := centralFreeFunctorMonoidal
  braided X Y := by
    apply (cancel_epi (Functor.OplaxMonoidal.δ (centralFreeFunctor (A := A)) X Y)).mp
    simp only [Functor.Monoidal.δ_μ_assoc]
    rw [centralFreeFunctor_δ_braiding_assoc, Functor.Monoidal.δ_μ]
    simp

end Paper18.Category.RelativeTensor
