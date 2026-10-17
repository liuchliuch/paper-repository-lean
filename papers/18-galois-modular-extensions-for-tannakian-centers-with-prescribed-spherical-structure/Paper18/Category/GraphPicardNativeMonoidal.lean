import Paper18.Category.GraphPicardNativeMonoidalNatIso
import Paper18.Category.GraphPicardNativeComparison

/-! # Genuine monoidal native-sign comparisons

The actual positive native alpha induction corresponds to the negative
central action, and negative native alpha induction corresponds to positive
central action. Simultaneously reversing the actual source and target tensor
orders retains these signs without imposing a braiding on module endofunctors.
The actual comparisons have identity underlying components; their tensor and
unit compatibility follow from the actual action associator and unitor.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite MonoidalLeftAction
open CategoryTheory.Functor.LaxMonoidal
universe v u vM uM
namespace Paper18.Category.GraphPicard
variable (D : Type u) [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  (M : Type uM) [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction Dᴹᵒᵖ M]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Linear ℂ]

/-- The genuine central-negative to native-positive comparison, after
simultaneously reversing both actual tensor orders. -/
def rightNegativeNativeMopIso :
    simultaneousMop (Drinfeld.negative D ⋙ rightCentralAction D M) ≅
      ModuleAlphaInduction.positiveMop Dᴹᵒᵖ M :=
  NatIso.ofComponents (fun X => Iso.mop ((rightNegativeNativeIso D M).app X.unmop))
    (fun {X Y} f => by
      apply Quiver.Hom.unmop_inj
      exact (rightNegativeNativeIso D M).hom.naturality f.unmop)

/-- The genuine central-positive to native-negative comparison. -/
def rightPositiveNativeMopIso :
    simultaneousMop (Drinfeld.positive D ⋙ rightCentralAction D M) ≅
      ModuleAlphaInduction.negativeMop Dᴹᵒᵖ M :=
  NatIso.ofComponents (fun X => Iso.mop ((rightPositiveNativeIso D M).app X.unmop))
    (fun {X Y} f => by
      apply Quiver.Hom.unmop_inj
      exact (rightPositiveNativeIso D M).hom.naturality f.unmop)

@[simp] theorem rightNegativeNativeMopIso_hom_app (X : Dᴹᵒᵖ) (m : M) :
    (((rightNegativeNativeMopIso D M).hom.app X).unmop).val.app m = 𝟙 (X ⊙ₗ m) := by
  change (𝟙 X) ⊵ₗ m = 𝟙 _
  simp
@[simp] theorem rightPositiveNativeMopIso_hom_app (X : Dᴹᵒᵖ) (m : M) :
    (((rightPositiveNativeMopIso D M).hom.app X).unmop).val.app m = 𝟙 (X ⊙ₗ m) := by
  change (𝟙 X) ⊵ₗ m = 𝟙 _
  simp

@[simp] theorem rightNegativeAction_μ_app (X Y : D) (m : M) :
    (μ (Drinfeld.negative D ⋙ rightCentralAction D M) X Y).val.app m =
      (αₗ (mop Y) (mop X) m).inv := by
  change (rightCentralTensorIso D M ((Drinfeld.negative D).obj X)
    ((Drinfeld.negative D).obj Y)).hom.val.app m ≫
      (𝟙 (mop (X ⊗ Y))) ⊵ₗ m = _
  rw [rightCentralTensorIso_hom_app]
  change (αₗ (mop Y) (mop X) m).inv ≫ (𝟙 (mop Y ⊗ mop X)) ⊵ₗ m = _
  rw [id_actionHomLeft]
  exact Category.comp_id _

@[simp] theorem rightPositiveAction_μ_app (X Y : D) (m : M) :
    (μ (Drinfeld.positive D ⋙ rightCentralAction D M) X Y).val.app m =
      (αₗ (mop Y) (mop X) m).inv := by
  change (rightCentralTensorIso D M ((Drinfeld.positive D).obj X)
    ((Drinfeld.positive D).obj Y)).hom.val.app m ≫
      (𝟙 (mop (X ⊗ Y))) ⊵ₗ m = _
  rw [rightCentralTensorIso_hom_app]
  change (αₗ (mop Y) (mop X) m).inv ≫ (𝟙 (mop Y ⊗ mop X)) ⊵ₗ m = _
  rw [id_actionHomLeft]
  exact Category.comp_id _

@[simp] theorem rightNegativeAction_ε_app (m : M) :
    (ε (Drinfeld.negative D ⋙ rightCentralAction D M)).val.app m =
      (λₗ[Dᴹᵒᵖ] m).inv := by
  change (rightCentralUnitIso D M).hom.val.app m ≫ (𝟙 (𝟙_ Dᴹᵒᵖ)) ⊵ₗ m = _
  rw [rightCentralUnitIso_hom_app]
  rw [id_actionHomLeft]
  exact Category.comp_id _

@[simp] theorem rightPositiveAction_ε_app (m : M) :
    (ε (Drinfeld.positive D ⋙ rightCentralAction D M)).val.app m =
      (λₗ[Dᴹᵒᵖ] m).inv := by
  change (rightCentralUnitIso D M).hom.val.app m ≫ (𝟙 (𝟙_ Dᴹᵒᵖ)) ⊵ₗ m = _
  rw [rightCentralUnitIso_hom_app]
  rw [id_actionHomLeft]
  exact Category.comp_id _

/-- Actual tensor and unit compatibility of the central-negative versus
native-positive comparison. -/
instance rightNegativeNativeMopIsoMonoidal :
    NatTrans.IsMonoidal (rightNegativeNativeMopIso D M).hom where
  unit := by
    apply Quiver.Hom.unmop_inj
    apply ModuleFunctor.bundled_hom_ext
    ext m
    change (ε (Drinfeld.negative D ⋙ rightCentralAction D M)).val.app m ≫
      (((rightNegativeNativeMopIso D M).hom.app (𝟙_ Dᴹᵒᵖ)).unmop).val.app m =
        ((ε (ModuleAlphaInduction.positiveMop Dᴹᵒᵖ M)).unmop).val.app m
    rw [rightNegativeAction_ε_app, rightNegativeNativeMopIso_hom_app,
      ModuleAlphaInduction.positiveMop_ε]
    exact Category.comp_id _
  tensor X Y := by
    apply Quiver.Hom.unmop_inj
    apply ModuleFunctor.bundled_hom_ext
    ext m
    change (μ (Drinfeld.negative D ⋙ rightCentralAction D M) Y.unmop X.unmop).val.app m ≫
      (((rightNegativeNativeMopIso D M).hom.app (X ⊗ Y)).unmop).val.app m =
        (((((rightNegativeNativeMopIso D M).hom.app X) ⊗ₘ
          ((rightNegativeNativeMopIso D M).hom.app Y)).unmop).val.app m) ≫
            ((μ (ModuleAlphaInduction.positiveMop Dᴹᵒᵖ M) X Y).unmop).val.app m
    simp only [rightNegativeAction_μ_app, rightNegativeNativeMopIso_hom_app,
      ModuleAlphaInduction.positiveMop_μ]
    change (αₗ X Y m).inv ≫ 𝟙 _ =
      ((𝟙 X) ⊵ₗ (Y ⊙ₗ m) ≫ X ⊴ₗ ((𝟙 Y) ⊵ₗ m)) ≫ (αₗ X Y m).inv
    simp only [id_actionHomLeft, actionHomRight_id, Category.id_comp, Category.comp_id]

/-- Actual tensor and unit compatibility of the central-positive versus
native-negative comparison. -/
instance rightPositiveNativeMopIsoMonoidal :
    NatTrans.IsMonoidal (rightPositiveNativeMopIso D M).hom where
  unit := by
    apply Quiver.Hom.unmop_inj
    apply ModuleFunctor.bundled_hom_ext
    ext m
    change (ε (Drinfeld.positive D ⋙ rightCentralAction D M)).val.app m ≫
      (((rightPositiveNativeMopIso D M).hom.app (𝟙_ Dᴹᵒᵖ)).unmop).val.app m =
        ((ε (ModuleAlphaInduction.negativeMop Dᴹᵒᵖ M)).unmop).val.app m
    rw [rightPositiveAction_ε_app, rightPositiveNativeMopIso_hom_app,
      ModuleAlphaInduction.negativeMop_ε]
    exact Category.comp_id _
  tensor X Y := by
    apply Quiver.Hom.unmop_inj
    apply ModuleFunctor.bundled_hom_ext
    ext m
    change (μ (Drinfeld.positive D ⋙ rightCentralAction D M) Y.unmop X.unmop).val.app m ≫
      (((rightPositiveNativeMopIso D M).hom.app (X ⊗ Y)).unmop).val.app m =
        (((((rightPositiveNativeMopIso D M).hom.app X) ⊗ₘ
          ((rightPositiveNativeMopIso D M).hom.app Y)).unmop).val.app m) ≫
            ((μ (ModuleAlphaInduction.negativeMop Dᴹᵒᵖ M) X Y).unmop).val.app m
    simp only [rightPositiveAction_μ_app, rightPositiveNativeMopIso_hom_app,
      ModuleAlphaInduction.negativeMop_μ]
    change (αₗ X Y m).inv ≫ 𝟙 _ =
      ((𝟙 X) ⊵ₗ (Y ⊙ₗ m) ≫ X ⊴ₗ ((𝟙 Y) ⊵ₗ m)) ≫ (αₗ X Y m).inv
    simp only [id_actionHomLeft, actionHomRight_id, Category.id_comp, Category.comp_id]

/-- Native positive alpha induction is monoidally the simultaneous
opposite of the genuine negative central action. -/
def nativePositiveMonoidalIso : ModuleAlphaInduction.positiveMop Dᴹᵒᵖ M ≅
    simultaneousMop (Drinfeld.negative D ⋙ rightCentralAction D M) :=
  (rightNegativeNativeMopIso D M).symm

/-- Native negative alpha induction is monoidally the simultaneous
opposite of the genuine positive central action. -/
def nativeNegativeMonoidalIso : ModuleAlphaInduction.negativeMop Dᴹᵒᵖ M ≅
    simultaneousMop (Drinfeld.positive D ⋙ rightCentralAction D M) :=
  (rightPositiveNativeMopIso D M).symm

instance nativePositiveMonoidalIsoMonoidal :
    NatTrans.IsMonoidal (nativePositiveMonoidalIso D M).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (rightNegativeNativeMopIso D M).inv)
instance nativeNegativeMonoidalIsoMonoidal :
    NatTrans.IsMonoidal (nativeNegativeMonoidalIso D M).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (rightPositiveNativeMopIso D M).inv)

end Paper18.Category.GraphPicard
