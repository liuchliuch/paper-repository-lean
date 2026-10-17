import Paper18.Category.GraphPicardCenterOpposite
import Paper18.Category.ModuleAlphaInductionMonoidal

/-! # The actual right central action as a tensor functor -/
noncomputable section
set_option maxHeartbeats 2000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite MonoidalLeftAction
universe v u vM uM
namespace Paper18.Category.GraphPicard
variable (D : Type u) [Category.{v} D] [MonoidalCategory D]
  (M : Type uM) [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction Dᴹᵒᵖ M]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Linear ℂ]

/-- The actual right central action keeps both its genuine module
lineators and the genuine additive complex-linear underlying functor. -/
def rightCentralAction : Center D ⥤ ModuleAlphaInduction.End Dᴹᵒᵖ M :=
  centerOpposite ⋙ ModuleAlphaInduction.centralAction Dᴹᵒᵖ M

/-- The actual two reversals, of center tensor order and endofunctor
composition order, give the genuine covariant tensor comparison. -/
def rightCentralTensorIso (Z W : Center D) :
    (rightCentralAction D M).obj Z ⊗ (rightCentralAction D M).obj W ≅
      (rightCentralAction D M).obj (Z ⊗ W) :=
  ModuleAlphaInduction.centralEndTensorIso Dᴹᵒᵖ M (centerOpposite.obj W)
      (centerOpposite.obj Z) ≪≫
    (ModuleAlphaInduction.centralAction Dᴹᵒᵖ M).mapIso (centerOppositeTensorIso Z W)

/-- The actual unit comparison uses the actual module unitor. -/
def rightCentralUnitIso :
    𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ M) ≅ (rightCentralAction D M).obj (𝟙_ (Center D)) :=
  ModuleAlphaInduction.centralEndUnitIso Dᴹᵒᵖ M ≪≫
    (ModuleAlphaInduction.centralAction Dᴹᵒᵖ M).mapIso centerOppositeUnitIso

@[simp] lemma rightCentralTensorIso_hom_app (Z W : Center D) (m : M) :
    (rightCentralTensorIso D M Z W).hom.val.app m =
      (αₗ (mop W.1) (mop Z.1) m).inv := by
  change (αₗ (mop W.1) (mop Z.1) m).inv ≫
    (𝟙 (mop (Z.1 ⊗ W.1))) ⊵ₗ m = _
  simp

@[simp] lemma rightCentralUnitIso_hom_app (m : M) :
    (rightCentralUnitIso D M).hom.val.app m = (λₗ[Dᴹᵒᵖ] m).inv := by
  change (λₗ[Dᴹᵒᵖ] m).inv ≫ (𝟙 (𝟙_ Dᴹᵒᵖ)) ⊵ₗ m = _
  simp

@[simp] lemma rightCentralAction_map_app {Z W : Center D} (q : Z ⟶ W) (m : M) :
    ((rightCentralAction D M).map q).val.app m = q.f.mop ⊵ₗ m := rfl

/-- Actual tensorator naturality in the first central factor. -/
lemma rightCentralTensorIso_naturality_left {Z Z' : Center D} (q : Z ⟶ Z') (W : Center D) :
    (rightCentralAction D M).map q ▷ (rightCentralAction D M).obj W ≫
        (rightCentralTensorIso D M Z' W).hom =
      (rightCentralTensorIso D M Z W).hom ≫ (rightCentralAction D M).map (q ▷ W) := by
  apply ModuleFunctor.bundled_hom_ext
  ext m
  change (mop W.1) ⊴ₗ q.f.mop ⊵ₗ m ≫
      (rightCentralTensorIso D M Z' W).hom.val.app m =
    (rightCentralTensorIso D M Z W).hom.val.app m ≫ ((q.f ▷ W.1).mop ⊵ₗ m)
  simp only [rightCentralTensorIso_hom_app]
  exact ModuleAlphaInduction.actionAssoc_inv_naturality_middle (mop W.1) q.f.mop m

/-- Actual tensorator naturality in the second central factor. -/
lemma rightCentralTensorIso_naturality_right {W W' : Center D} (Z : Center D) (q : W ⟶ W') :
    (rightCentralAction D M).obj Z ◁ (rightCentralAction D M).map q ≫
        (rightCentralTensorIso D M Z W').hom =
      (rightCentralTensorIso D M Z W).hom ≫ (rightCentralAction D M).map (Z ◁ q) := by
  apply ModuleFunctor.bundled_hom_ext
  ext m
  change q.f.mop ⊵ₗ ((mop Z.1) ⊙ₗ m) ≫
      (rightCentralTensorIso D M Z W').hom.val.app m =
    (rightCentralTensorIso D M Z W).hom.val.app m ≫ ((Z.1 ◁ q.f).mop ⊵ₗ m)
  simp only [rightCentralTensorIso_hom_app]
  rw [MonoidalLeftAction.actionHomLeft_action]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl


/-- The genuine right central action preserves tensor products and the
unit, with coherence inherited from the actual module pentagon. -/
instance rightCentralActionMonoidal : (rightCentralAction D M).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := rightCentralUnitIso D M
      μIso := rightCentralTensorIso D M
      μIso_hom_natural_left := rightCentralTensorIso_naturality_left D M
      μIso_hom_natural_right := rightCentralTensorIso_naturality_right D M
      associativity Z W V := by
        apply ModuleFunctor.bundled_hom_ext
        ext m
        change (mop V.1) ⊴ₗ (rightCentralTensorIso D M Z W).hom.val.app m ≫
          (rightCentralTensorIso D M (Z ⊗ W) V).hom.val.app m ≫
          ((α_ Z.1 W.1 V.1).hom.mop ⊵ₗ m) =
          𝟙 _ ≫ (rightCentralTensorIso D M W V).hom.val.app ((mop Z.1) ⊙ₗ m) ≫
            (rightCentralTensorIso D M Z (W ⊗ V)).hom.val.app m
        simp only [rightCentralTensorIso_hom_app, Category.id_comp]
        change (mop V.1) ⊴ₗ (αₗ (mop W.1) (mop Z.1) m).inv ≫
          (αₗ (mop V.1) (mop W.1 ⊗ mop Z.1) m).inv ≫
          ((α_ (mop V.1) (mop W.1) (mop Z.1)).inv ⊵ₗ m) =
          (αₗ (mop V.1) (mop W.1) ((mop Z.1) ⊙ₗ m)).inv ≫
          (αₗ (mop V.1 ⊗ mop W.1) (mop Z.1) m).inv
        rw [ModuleAlphaInduction.associator_action_inv]
        simp only [Category.assoc, Iso.inv_hom_id_assoc,
          MonoidalLeftAction.actionHomRight_inv_hom_assoc]
      left_unitality Z := by
        apply ModuleFunctor.bundled_hom_ext
        ext m
        change 𝟙 _ = (mop Z.1) ⊴ₗ (rightCentralUnitIso D M).hom.val.app m ≫
          (rightCentralTensorIso D M (𝟙_ (Center D)) Z).hom.val.app m ≫
          ((λ_ Z.1).hom.mop ⊵ₗ m)
        simp only [rightCentralUnitIso_hom_app, rightCentralTensorIso_hom_app]
        change 𝟙 _ = (mop Z.1) ⊴ₗ (λₗ m).inv ≫
          (αₗ (mop Z.1) (𝟙_ Dᴹᵒᵖ) m).inv ≫ ((ρ_ (mop Z.1)).hom ⊵ₗ m)
        rw [rightUnitor_actionHom]
        simp
      right_unitality Z := by
        apply ModuleFunctor.bundled_hom_ext
        ext m
        change 𝟙 _ = (rightCentralUnitIso D M).hom.val.app ((mop Z.1) ⊙ₗ m) ≫
          (rightCentralTensorIso D M Z (𝟙_ (Center D))).hom.val.app m ≫
          ((ρ_ Z.1).hom.mop ⊵ₗ m)
        simp only [rightCentralUnitIso_hom_app, rightCentralTensorIso_hom_app]
        change 𝟙 _ = (λₗ ((mop Z.1) ⊙ₗ m)).inv ≫
          (αₗ (𝟙_ Dᴹᵒᵖ) (mop Z.1) m).inv ≫ ((λ_ (mop Z.1)).hom ⊵ₗ m)
        rw [leftUnitor_actionHom]
        simp }

end Paper18.Category.GraphPicard
