import Paper18.Category.RelativeCenterInductionHomBasic

/-! # Actual supported relative induction and its genuine Hom correspondence -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category.RelativeCenter
open Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)] [BraidedCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {P : ObjectProperty C} [P.IsMonoidal] [IsAdditiveFullProperty P]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

/-- Actual relative-central projection of ambient induction onto its chosen
subcategory labels, obtained from the actual relative augmentation. -/
def inductionSupportEnd (X : C) :
    (restriction P).obj (inductionObj S J X) ⟶ (restriction P).obj (inductionObj S J X) :=
  augmentationHom S J ((restriction P).obj (inductionObj S J X)) (inductionAdjunctionUnit J S X)

@[reassoc]
lemma inductionι_supportEnd (X : C) (i : ι) :
    inductionι S X (S.simpleObject i) ≫ (inductionSupportEnd (P := P) S J X).f =
      if P (S.simpleObject i) then inductionι S X (S.simpleObject i) else 0 := by
  change inductionι S X (S.simpleObject i) ≫
    augmentation S J ((restriction P).obj (inductionObj S J X)) (inductionAdjunctionUnit J S X) = _
  rw [inductionι_augmentation_simple]
  by_cases hi : P (S.simpleObject i)
  · rw [dif_pos hi, if_pos hi]
    have hr := Drinfeld.inductionAugmentation_recover J S (inductionObj S J X)
      (𝟙 (inductionUnderlying S X)) (by intro U; simp)
    simp only [comp_id] at hr
    have ht := congrArg (fun k => inductionι S X (S.simpleObject i) ≫ k) hr
    dsimp only at ht
    rw [Drinfeld.inductionι_augmentation, comp_id] at ht
    exact ht
  · rw [dif_neg hi, if_neg hi]

lemma inductionSupportEnd_idempotent (X : C) :
    inductionSupportEnd (P := P) S J X ≫ inductionSupportEnd S J X = inductionSupportEnd S J X := by
  apply ext P
  apply induction_hom_ext_simple S
  intro i
  change inductionι S X (S.simpleObject i) ≫
    ((inductionSupportEnd S J X).f ≫ (inductionSupportEnd S J X).f) = _
  rw [← assoc, inductionι_supportEnd]
  by_cases hi : P (S.simpleObject i) <;> simp [hi, inductionι_supportEnd]

/-- The relative induction object is the actual kernel image of the proved
relative-central idempotent. No idempotent-splitting certificate is an input. -/
def inductionObject (X : C) : RelativeCenter P :=
  kernelObj (𝟙 ((restriction P).obj (inductionObj S J X)) - inductionSupportEnd S J X)

def inductionInclusion (X : C) : inductionObject (P := P) S J X ⟶
    (restriction P).obj (inductionObj S J X) := kernelι _

instance inductionInclusion_mono (X : C) : Mono (inductionInclusion (P := P) S J X) :=
  inferInstanceAs (Mono (kernelι _))

@[reassoc]
lemma inductionInclusion_supportEnd (X : C) :
    inductionInclusion (P := P) S J X ≫ inductionSupportEnd S J X = inductionInclusion S J X := by
  have h := kernelι_condition
    (𝟙 ((restriction P).obj (inductionObj S J X)) - inductionSupportEnd (P := P) S J X)
  change inductionInclusion S J X ≫ (𝟙 _ - inductionSupportEnd S J X) = 0 at h
  rw [Preadditive.comp_sub, comp_id] at h
  exact (sub_eq_zero.mp h).symm

def inductionProjection (X : C) : (restriction P).obj (inductionObj S J X) ⟶
    inductionObject (P := P) S J X :=
  kernelLift _ (inductionSupportEnd S J X) (by
    rw [Preadditive.comp_sub, comp_id, inductionSupportEnd_idempotent, sub_self])

@[simp, reassoc]
lemma inductionProjection_inclusion (X : C) :
    inductionProjection (P := P) S J X ≫ inductionInclusion S J X = inductionSupportEnd S J X :=
  kernelLift_ι _ _ _

@[simp, reassoc]
lemma inductionInclusion_projection (X : C) :
    inductionInclusion (P := P) S J X ≫ inductionProjection S J X = 𝟙 _ := by
  apply (cancel_mono (inductionInclusion S J X)).mp
  rw [assoc, inductionProjection_inclusion, id_comp, inductionInclusion_supportEnd]

@[reassoc]
lemma inductionSupportEnd_projection (X : C) :
    inductionSupportEnd (P := P) S J X ≫ inductionProjection S J X = inductionProjection S J X := by
  rw [← inductionProjection_inclusion S J X, assoc, inductionInclusion_projection, comp_id]

lemma inductionι_projection_outside (X : C) (i : ι) (hi : ¬ P (S.simpleObject i)) :
    inductionι S X (S.simpleObject i) ≫ (inductionProjection (P := P) S J X).f = 0 := by
  have h := congrArg (fun k => inductionι S X (S.simpleObject i) ≫ k.f)
    (inductionSupportEnd_projection (P := P) S J X)
  change inductionι S X (S.simpleObject i) ≫
    ((inductionSupportEnd S J X).f ≫ (inductionProjection S J X).f) = _ at h
  rw [← assoc, inductionι_supportEnd, if_neg hi, zero_comp] at h
  exact h.symm

lemma inductionSupportEnd_augmentation (Z : RelativeCenter P) {X : C} (f : X ⟶ Z.1) :
    (inductionSupportEnd (P := P) S J X).f ≫ augmentation S J Z f = augmentation S J Z f := by
  apply induction_hom_ext_simple S
  intro i
  rw [← assoc, inductionι_supportEnd]
  by_cases hi : P (S.simpleObject i)
  · rw [if_pos hi]
  · rw [if_neg hi, zero_comp, inductionι_augmentation_simple, dif_neg hi]

/-- The actual unit insertion into the supported relative induction object. -/
def inductionUnit (X : C) : X ⟶ (inductionObject (P := P) S J X).1 :=
  inductionAdjunctionUnit J S X ≫ (inductionProjection S J X).f

set_option maxHeartbeats 1000000 in
/-- The genuine complex-linear Hom correspondence for actual relative
induction, derived from the actual supported idempotent and cup/cap identities. -/
def inductionHomLinearEquiv (X : C) (Z : RelativeCenter P) :
    (inductionObject (P := P) S J X ⟶ Z) ≃ₗ[ℂ] (X ⟶ Z.1) where
  toFun h := inductionUnit S J X ≫ h.f
  invFun f := inductionInclusion S J X ≫ augmentationHom S J Z f
  left_inv h := by
    let r : (restriction P).obj (inductionObj S J X) ⟶ Z := inductionProjection S J X ≫ h
    have hs (i : ι) (hi : ¬ P (S.simpleObject i)) : inductionι S X (S.simpleObject i) ≫ r.f = 0 := by
      change inductionι S X (S.simpleObject i) ≫ ((inductionProjection S J X).f ≫ h.f) = 0
      rw [← assoc, inductionι_projection_outside S J X i hi, zero_comp]
    have hr := augmentation_recover_supported J S Z r hs
    apply ext P
    change (inductionInclusion S J X).f ≫
      augmentation S J Z (inductionUnit S J X ≫ h.f) = h.f
    have hu : inductionUnit S J X ≫ h.f = inductionAdjunctionUnit J S X ≫ r.f := by
      simp only [inductionUnit, r, comp_f, assoc]
    rw [hu, hr]
    change (inductionInclusion S J X ≫ inductionProjection S J X ≫ h).f = h.f
    rw [← assoc, inductionInclusion_projection, id_comp]
  right_inv f := by
    change (inductionAdjunctionUnit J S X ≫ (inductionProjection S J X).f) ≫
      ((inductionInclusion S J X).f ≫ augmentation S J Z f) = f
    have he : (inductionProjection (P := P) S J X).f ≫ (inductionInclusion S J X).f =
        (inductionSupportEnd S J X).f := congrArg Hom.f (inductionProjection_inclusion S J X)
    simp only [assoc]
    rw [← assoc (inductionProjection S J X).f, he, inductionSupportEnd_augmentation,
      adjunctionUnit_augmentation]
  map_add' h k := by simp only [add_f, Preadditive.comp_add]
  map_smul' c h := by simp only [smul_f, Linear.comp_smul, RingHom.id_apply]

end Paper18.Category.RelativeCenter
