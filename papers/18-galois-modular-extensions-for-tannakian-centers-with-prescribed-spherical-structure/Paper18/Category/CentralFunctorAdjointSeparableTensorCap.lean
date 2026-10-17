import Paper18.Category.CentralFunctorAdjointSeparableCapDinatural
import Paper18.Category.PivotalFunctorTensorBasic

/-! # Tensor caps transported to arbitrary native actions

Only the specified caps are used. In particular, the category acted on
need not carry a monoidal structure or chosen duals.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
open scoped MonoidalLeftAction
universe v u vD uD vM uM vN uN
namespace Paper18.Category.CentralFunctorAdjointSeparable
open MonoidalLeftAction

section ArbitraryMonoidal
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal]

/-- The tensor-cap preservation identity needs no global rigidity
assumption on either category. -/
lemma map_tensorCap (X Y DX DY : C) (ex : DX ⊗ X ⟶ 𝟙_ C)
    (ey : DY ⊗ Y ⟶ 𝟙_ C) :
    (μ F DY DX ⊗ₘ μ F X Y) ≫ μ F (DY ⊗ DX) (X ⊗ Y) ≫
        F.map (tensorEval X Y DX DY ex ey) ≫ η F =
      tensorEval (F.obj X) (F.obj Y) (F.obj DX) (F.obj DY)
        (μ F DX X ≫ F.map ex ≫ η F) (μ F DY Y ≫ F.map ey ≫ η F) := by
  dsimp only [tensorEval]
  simp only [Functor.map_comp, Functor.Monoidal.map_associator,
    Functor.Monoidal.map_associator_inv, Functor.Monoidal.map_whiskerLeft,
    Functor.Monoidal.map_whiskerRight, Functor.Monoidal.map_leftUnitor, Category.assoc]
  simp only [μ_δ_assoc, MonoidalCategory.whiskerLeft_comp,
    comp_whiskerRight, Category.assoc]
  rw [tensorHom_def']
  simp only [Category.assoc, ← comp_whiskerRight_assoc, μ_δ,
    id_whiskerRight, Category.id_comp]
  rw [associator_naturality_right_assoc]
  simp only [μ_δ_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, μ_δ,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

end ArbitraryMonoidal

section NativeAction
attribute [local instance] endofunctorMonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (M : Type uM) [Category.{vM} M] [MonoidalLeftAction C M]

/-- The actual cap induced by an arbitrary acting-category cap. -/
def actionCap {P X : C} (b : P ⊗ X ⟶ 𝟙_ C) (m : M) :
    P ⊙ₗ X ⊙ₗ m ⟶ m :=
  (αₗ P X m).inv ≫ b ⊵ₗ m ≫ (λₗ[C] m).hom

/-- Nested tensor caps in a native action are the actual composite of
the two original native caps. -/
lemma actionCap_tensor (X Y DX DY : C) (ex : DX ⊗ X ⟶ 𝟙_ C)
    (ey : DY ⊗ Y ⟶ 𝟙_ C) (m : M) :
    (αₗ DY DX ((X ⊗ Y) ⊙ₗ m)).inv ≫
        actionCap M (tensorEval X Y DX DY ex ey) m =
      (DY ⊴ₗ (DX ⊴ₗ (αₗ X Y m).hom)) ≫
        (DY ⊴ₗ actionCap M ex (Y ⊙ₗ m)) ≫ actionCap M ey m := by
  have h := congrArg (fun f => f.unmop.app m)
    (map_tensorCap (curriedActionMop C M) X Y DX DY ex ey)
  dsimp [curriedActionMopMonoidal, tensorEval] at h
  simp only [Category.id_comp, Category.comp_id, Category.assoc] at h
  rw [tensor_actionHomRight] at h
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at h
  apply (cancel_epi (DY ⊴ₗ (DX ⊴ₗ (αₗ X Y m).inv))).mp
  simpa only [actionCap, Category.assoc, ← actionHomRight_comp_assoc,
    ← actionHomRight_comp, Iso.inv_hom_id, actionHomRight_id, Category.id_comp] using h

end NativeAction

section ModuleFunctor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type uM} [Category.{vM} M] [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [MonoidalLeftAction C N]
  (F : M ⥤ N) [F.LeftLinear C]

/-- The actual lineator followed by the image of an arbitrary native cap. -/
def functorCap {P X : C} (b : P ⊗ X ⟶ 𝟙_ C) (m : M) :
    P ⊙ₗ F.obj (X ⊙ₗ m) ⟶ F.obj m :=
  Functor.LaxLeftLinear.μₗ F P (X ⊙ₗ m) ≫ F.map (actionCap M b m)

@[simp] lemma functorCap_evaluation (X DX : C) [ExactPairing X DX] (m : M) :
    functorCap F (ε_ X DX) m = (capComponent F X DX).app m := rfl

/-- Cap coordinates transport actual maps on the first external factor. -/
lemma functorCap_map_left {P P' X : C} (f : P ⟶ P')
    (b : P' ⊗ X ⟶ 𝟙_ C) (m : M) :
    f ⊵ₗ F.obj (X ⊙ₗ m) ≫ functorCap F b m =
      functorCap F (f ▷ X ≫ b) m := by
  dsimp only [functorCap, actionCap]
  rw [← Category.assoc, Functor.LaxLeftLinear.μₗ_naturality_left]
  simp only [Category.assoc, ← F.map_comp]
  congr 2
  rw [comp_actionHomLeft, whiskerRight_actionHomLeft]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Cap coordinates transport actual maps on the second external factor. -/
lemma functorCap_map_right {P X X' : C} (f : X ⟶ X')
    (b : P ⊗ X' ⟶ 𝟙_ C) (m : M) :
    P ⊴ₗ F.map (f ⊵ₗ m) ≫ functorCap F b m =
      functorCap F (P ◁ f ≫ b) m := by
  dsimp only [functorCap, actionCap]
  rw [← Category.assoc, Functor.LaxLeftLinear.μₗ_naturality_right]
  simp only [Category.assoc, ← F.map_comp]
  congr 2
  rw [comp_actionHomLeft, whiskerLeft_actionHomLeft]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The actual unit cap is the native action unit on both sides of the
actual functor. -/
lemma functorCap_unit (m : M) :
    functorCap F (λ_ (𝟙_ C)).hom m =
      (λₗ[C] (F.obj ((𝟙_ C) ⊙ₗ m))).hom ≫ F.map (λₗ[C] m).hom := by
  dsimp only [functorCap, actionCap]
  rw [leftUnitor_actionHom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, F.map_comp]
  rw [← Category.assoc, ← Functor.LaxLeftLinear.μₗ_unitality]

/-- Tensoring labels composes the two genuine lineator-cap coordinates.
This is the actual multiplicativity needed for diagonal averaging. -/
lemma functorCap_tensor (X Y DX DY : C) (ex : DX ⊗ X ⟶ 𝟙_ C)
    (ey : DY ⊗ Y ⟶ 𝟙_ C) (m : M) :
    (αₗ DY DX (F.obj ((X ⊗ Y) ⊙ₗ m))).inv ≫
        functorCap F (tensorEval X Y DX DY ex ey) m =
      (DY ⊴ₗ (DX ⊴ₗ F.map (αₗ X Y m).hom)) ≫
        (DY ⊴ₗ functorCap F ex (Y ⊙ₗ m)) ≫ functorCap F ey m := by
  dsimp only [functorCap]
  rw [← Category.assoc, ← Functor.LaxLeftLinear.μₗ_associativity_inv]
  simp only [Category.assoc, ← F.map_comp]
  rw [actionCap_tensor]
  simp only [F.map_comp]
  rw [← Functor.LaxLeftLinear.μₗ_naturality_right_assoc]
  rw [← Functor.LaxLeftLinear.μₗ_naturality_right_assoc]
  simp only [← actionHomRight_comp_assoc]
  rw [← Functor.LaxLeftLinear.μₗ_naturality_right_assoc]

end ModuleFunctor

section ChosenDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
attribute [local instance 2000] RightRigidCategory.rightDual
variable {M : Type uM} [Category.{vM} M] [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [MonoidalLeftAction C N]
  (F : M ⥤ N) [F.LeftLinear C]

/-- The actual chosen-dual unit insertion acts by the genuine native
unit constraint of the functor. -/
lemma capComponent_unit (m : M) :
    (dualUnitIso (C := C)).inv ⊵ₗ F.obj ((𝟙_ C) ⊙ₗ m) ≫
        (capComponent F (𝟙_ C) (𝟙_ C)ᘁ).app m =
      (λₗ[C] (F.obj ((𝟙_ C) ⊙ₗ m))).hom ≫ F.map (λₗ[C] m).hom := by
  rw [← functorCap_evaluation, functorCap_map_left, dualUnitIso_inv_evaluation,
    ← unitors_equal, functorCap_unit]

/-- The chosen actual dual comparison identifies the composite-label cap
with the actual tensor cap. -/
lemma capComponent_dualTensor (X Y : C) (m : M) :
    (dualTensorIso X Y).inv ⊵ₗ F.obj ((X ⊗ Y) ⊙ₗ m) ≫
        (capComponent F (X ⊗ Y) (X ⊗ Y)ᘁ).app m =
      functorCap F (tensorEvaluation C X Y) m := by
  rw [← functorCap_evaluation, functorCap_map_left, dualTensorIso_inv_evaluation]

/-- Multiplying actual labels composes their true cap coordinates; all
dual and action associators are specified in the equation. -/
lemma capComponent_tensor (X Y : C) (m : M) :
    (αₗ Yᘁ Xᘁ (F.obj ((X ⊗ Y) ⊙ₗ m))).inv ≫
        (dualTensorIso X Y).inv ⊵ₗ F.obj ((X ⊗ Y) ⊙ₗ m) ≫
          (capComponent F (X ⊗ Y) (X ⊗ Y)ᘁ).app m =
      (Yᘁ ⊴ₗ (Xᘁ ⊴ₗ F.map (αₗ X Y m).hom)) ≫
        (Yᘁ ⊴ₗ (capComponent F X Xᘁ).app (Y ⊙ₗ m)) ≫
          (capComponent F Y Yᘁ).app m := by
  rw [capComponent_dualTensor]
  simpa only [functorCap_evaluation, tensorEvaluation_eq] using
    functorCap_tensor F X Y Xᘁ Yᘁ (ε_ X Xᘁ) (ε_ Y Yᘁ) m

end ChosenDual
end Paper18.Category.CentralFunctorAdjointSeparable
