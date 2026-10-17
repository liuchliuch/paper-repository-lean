import Paper18.Category.PivotalDuality
import Mathlib.CategoryTheory.Monoidal.Opposite

/-!
# Canonical double-dual coherence from rigidity

This file develops the tensor coherence of the chosen duality without assuming
that the category has a pivotal structure. The pivotal structure of an ambient
fusion category must not be an input to sphericalization.
-/
noncomputable section
universe v u
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- Tensor evaluation for arbitrary specified caps, used to compare chosen
and canonical tensor duals without a pivotal structure. -/
def tensorEval (X Y Xd Yd : C) (ex : Xd ⊗ X ⟶ 𝟙_ C) (ey : Yd ⊗ Y ⟶ 𝟙_ C) :
    (Yd ⊗ Xd) ⊗ (X ⊗ Y) ⟶ 𝟙_ C :=
  (α_ Yd Xd (X ⊗ Y)).hom ≫
    Yd ◁ ((α_ Xd X Y).inv ≫ ex ▷ Y ≫ (λ_ Y).hom) ≫ ey

lemma tensorEvaluation_eq (X Y : C) : tensorEvaluation C X Y =
    tensorEval X Y (dual C X) (dual C Y) (ε_ X (dual C X)) (ε_ Y (dual C Y)) := rfl

lemma tensorEval_map_leftDual {X Y Xd Xd' Yd : C}
    (ex : Xd ⊗ X ⟶ 𝟙_ C) (ey : Yd ⊗ Y ⟶ 𝟙_ C) (s : Xd' ⟶ Xd) :
    (Yd ◁ s) ▷ (X ⊗ Y) ≫ tensorEval X Y Xd Yd ex ey =
      tensorEval X Y Xd' Yd (s ▷ X ≫ ex) ey := by
  dsimp [tensorEval]
  monoidal

lemma tensorEval_map_rightDual {X Y Xd Yd Yd' : C}
    (ex : Xd ⊗ X ⟶ 𝟙_ C) (ey : Yd ⊗ Y ⟶ 𝟙_ C) (t : Yd' ⟶ Yd) :
    (t ▷ Xd) ▷ (X ⊗ Y) ≫ tensorEval X Y Xd Yd ex ey =
      tensorEval X Y Xd Yd' ex (t ▷ Y ≫ ey) := by
  calc
    _ = 𝟙 ((Yd' ⊗ Xd) ⊗ (X ⊗ Y)) ⊗≫
        (t ▷ ((Xd ⊗ X) ⊗ Y) ≫ Yd ◁ (ex ▷ Y)) ⊗≫ ey ⊗≫ 𝟙 (𝟙_ C) := by
      dsimp [tensorEval]
      monoidal
    _ = _ := by
      rw [← whisker_exchange]
      dsimp [tensorEval]
      monoidal

lemma tensorEval_associativity (X Y Z Xd Yd Zd : C)
    (ex : Xd ⊗ X ⟶ 𝟙_ C) (ey : Yd ⊗ Y ⟶ 𝟙_ C) (ez : Zd ⊗ Z ⟶ 𝟙_ C) :
    (α_ Zd Yd Xd).hom ▷ ((X ⊗ Y) ⊗ Z) ≫
        tensorEval (X ⊗ Y) Z (Yd ⊗ Xd) Zd (tensorEval X Y Xd Yd ex ey) ez =
      ((Zd ⊗ Yd) ⊗ Xd) ◁ (α_ X Y Z).hom ≫
        tensorEval X (Y ⊗ Z) Xd (Zd ⊗ Yd) ex (tensorEval Y Z Yd Zd ey ez) := by
  dsimp [tensorEval]
  monoidal

/-- Naturality of the tensor evaluation in its first paired factor. -/
lemma tensorEvaluation_naturality_left {X X' : C} (f : X ⟶ X') (Y : C) :
    (dual C Y ◁ dualMap C f) ▷ (X ⊗ Y) ≫ tensorEvaluation C X Y =
      (dual C Y ⊗ dual C X') ◁ (f ▷ Y) ≫ tensorEvaluation C X' Y := by
  calc
    _ = 𝟙 ((dual C Y ⊗ dual C X') ⊗ (X ⊗ Y)) ⊗≫
        dual C Y ◁ (dualMap C f ▷ X ≫ ε_ X (dual C X)) ▷ Y ⊗≫
        ε_ Y (dual C Y) ⊗≫ 𝟙 (𝟙_ C) := by
      dsimp [tensorEvaluation]
      monoidal
    _ = _ := by
      rw [rightAdjointMate_comp_evaluation f]
      dsimp [tensorEvaluation]
      monoidal

/-- Naturality of the tensor evaluation in its second paired factor. -/
lemma tensorEvaluation_naturality_right (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    (dualMap C g ▷ dual C X) ▷ (X ⊗ Y) ≫ tensorEvaluation C X Y =
      (dual C Y' ⊗ dual C X) ◁ (X ◁ g) ≫ tensorEvaluation C X Y' := by
  calc
    _ = 𝟙 ((dual C Y' ⊗ dual C X) ⊗ (X ⊗ Y)) ⊗≫
        (dualMap C g ▷ ((dual C X ⊗ X) ⊗ Y) ≫
          dual C Y ◁ (ε_ X (dual C X) ▷ Y)) ⊗≫
        ε_ Y (dual C Y) ⊗≫ 𝟙 (𝟙_ C) := by
      dsimp [tensorEvaluation]
      monoidal
    _ = 𝟙 ((dual C Y' ⊗ dual C X) ⊗ (X ⊗ Y)) ⊗≫
        dual C Y' ◁ ε_ X (dual C X) ▷ Y ⊗≫
        (dualMap C g ▷ Y ≫ ε_ Y (dual C Y)) ⊗≫ 𝟙 (𝟙_ C) := by
      rw [← whisker_exchange]
      monoidal
    _ = 𝟙 ((dual C Y' ⊗ dual C X) ⊗ (X ⊗ Y)) ⊗≫
        dual C Y' ◁ (ε_ X (dual C X) ▷ Y ≫ 𝟙_ C ◁ g) ⊗≫
        ε_ Y' (dual C Y') ⊗≫ 𝟙 (𝟙_ C) := by
      rw [rightAdjointMate_comp_evaluation g]
      monoidal
    _ = _ := by
      rw [← whisker_exchange]
      dsimp [tensorEvaluation]
      monoidal

lemma dualTensorIso_evaluation (X Y : C) :
    (dualTensorIso X Y).hom ▷ (X ⊗ Y) ≫ tensorEvaluation C X Y =
      ε_ (X ⊗ Y) (dual C (X ⊗ Y)) :=
  rightDualIso_evaluation _ (tensorExactPairing X Y)

/-- Contravariant naturality of the canonical dual tensor comparison on the left. -/
lemma dualTensorIso_naturality_left {X X' : C} (f : X ⟶ X') (Y : C) :
    dualMap C (f ▷ Y) ≫ (dualTensorIso X Y).hom =
      (dualTensorIso X' Y).hom ≫ dual C Y ◁ dualMap C f := by
  apply pairing_hom_ext (tensorExactPairing X Y)
  change _ ▷ (X ⊗ Y) ≫ tensorEvaluation C X Y =
    _ ▷ (X ⊗ Y) ≫ tensorEvaluation C X Y
  simp only [comp_whiskerRight, assoc]
  rw [dualTensorIso_evaluation, tensorEvaluation_naturality_left,
    ← whisker_exchange_assoc, dualTensorIso_evaluation,
    rightAdjointMate_comp_evaluation]

/-- Contravariant naturality of the canonical dual tensor comparison on the right. -/
lemma dualTensorIso_naturality_right (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    dualMap C (X ◁ g) ≫ (dualTensorIso X Y).hom =
      (dualTensorIso X Y').hom ≫ dualMap C g ▷ dual C X := by
  apply pairing_hom_ext (tensorExactPairing X Y)
  change _ ▷ (X ⊗ Y) ≫ tensorEvaluation C X Y =
    _ ▷ (X ⊗ Y) ≫ tensorEvaluation C X Y
  simp only [comp_whiskerRight, assoc]
  rw [dualTensorIso_evaluation, tensorEvaluation_naturality_right,
    ← whisker_exchange_assoc, dualTensorIso_evaluation,
    rightAdjointMate_comp_evaluation]

/-- Full contravariant tensor naturality, proved from the actual evaluations. -/
lemma dualTensorIso_naturality {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    dualMap C (f ⊗ₘ g) ≫ (dualTensorIso X Y).hom =
      (dualTensorIso X' Y').hom ≫ (dualMap C g ⊗ₘ dualMap C f) := by
  rw [tensorHom_def]
  dsimp only [dualMap]
  rw [comp_rightAdjointMate, assoc, dualTensorIso_naturality_left,
    ← assoc, dualTensorIso_naturality_right, assoc, ← tensorHom_def]

/-- Associativity of tensor caps after the canonical dual comparisons. -/
lemma tensorEvaluation_associativity (X Y Z : C) :
    (α_ (dual C Z) (dual C Y) (dual C X)).hom ▷ ((X ⊗ Y) ⊗ Z) ≫
      (dual C Z ◁ (dualTensorIso X Y).inv) ▷ ((X ⊗ Y) ⊗ Z) ≫
        tensorEvaluation C (X ⊗ Y) Z =
      ((dualTensorIso Y Z).inv ▷ dual C X) ▷ ((X ⊗ Y) ⊗ Z) ≫
        (dual C (Y ⊗ Z) ⊗ dual C X) ◁ (α_ X Y Z).hom ≫ tensorEvaluation C X (Y ⊗ Z) := by
  simp only [tensorEvaluation_eq]
  rw [tensorEval_map_leftDual, dualTensorIso_inv_evaluation]
  rw [← whisker_exchange_assoc (f := (dualTensorIso Y Z).inv ▷ dual C X)
    (g := (α_ X Y Z).hom)]
  rw [tensorEval_map_rightDual, dualTensorIso_inv_evaluation]
  exact tensorEval_associativity X Y Z (dual C X) (dual C Y) (dual C Z) _ _ _

/-- The anti-tensor comparison satisfies associativity coherence. -/
lemma dualTensorIso_associativity (X Y Z : C) :
    dualMap C (α_ X Y Z).hom ≫ (dualTensorIso (X ⊗ Y) Z).hom ≫
      dual C Z ◁ (dualTensorIso X Y).hom =
    (dualTensorIso X (Y ⊗ Z)).hom ≫ (dualTensorIso Y Z).hom ▷ dual C X ≫
      (α_ (dual C Z) (dual C Y) (dual C X)).hom := by
  apply (cancel_mono (dual C Z ◁ (dualTensorIso X Y).inv)).1
  apply pairing_hom_ext (tensorExactPairing (X ⊗ Y) Z)
  change _ ▷ ((X ⊗ Y) ⊗ Z) ≫ tensorEvaluation C (X ⊗ Y) Z =
    _ ▷ ((X ⊗ Y) ⊗ Z) ≫ tensorEvaluation C (X ⊗ Y) Z
  simp only [assoc, comp_whiskerRight]
  have hc : (dual C Z ◁ (dualTensorIso X Y).hom) ▷ ((X ⊗ Y) ⊗ Z) ≫
      (dual C Z ◁ (dualTensorIso X Y).inv) ▷ ((X ⊗ Y) ⊗ Z) = 𝟙 _ := by
    rw [← comp_whiskerRight, ← whiskerLeft_comp, Iso.hom_inv_id,
      whiskerLeft_id, id_whiskerRight]
  rw [reassoc_of% hc]
  rw [dualTensorIso_evaluation, rightAdjointMate_comp_evaluation,
    tensorEvaluation_associativity]
  have hc2 : (dualTensorIso Y Z).hom ▷ dual C X ▷ ((X ⊗ Y) ⊗ Z) ≫
      (dualTensorIso Y Z).inv ▷ dual C X ▷ ((X ⊗ Y) ⊗ Z) = 𝟙 _ := by
    rw [← comp_whiskerRight, ← comp_whiskerRight, Iso.hom_inv_id,
      id_whiskerRight, id_whiskerRight]
  rw [reassoc_of% hc2, ← whisker_exchange_assoc, dualTensorIso_evaluation]

/-- The anti-tensor comparison is compatible with the left unitor. -/
lemma dualTensorIso_leftUnitor (X : C) :
    dualMap C (λ_ X).hom ≫ (dualTensorIso (𝟙_ C) X).hom =
      (ρ_ (dual C X)).inv ≫ dual C X ◁ (dualUnitIso (C := C)).inv := by
  apply pairing_hom_ext (tensorExactPairing (𝟙_ C) X)
  change _ ▷ ((𝟙_ C) ⊗ X) ≫ tensorEvaluation C (𝟙_ C) X =
    _ ▷ ((𝟙_ C) ⊗ X) ≫ tensorEvaluation C (𝟙_ C) X
  simp only [comp_whiskerRight, assoc]
  rw [dualTensorIso_evaluation, rightAdjointMate_comp_evaluation,
    tensorEvaluation_eq, tensorEval_map_leftDual, dualUnitIso_inv_evaluation]
  dsimp [tensorEval]
  monoidal

/-- The anti-tensor comparison is compatible with the right unitor. -/
lemma dualTensorIso_rightUnitor (X : C) :
    dualMap C (ρ_ X).hom ≫ (dualTensorIso X (𝟙_ C)).hom =
      (λ_ (dual C X)).inv ≫ (dualUnitIso (C := C)).inv ▷ dual C X := by
  apply pairing_hom_ext (tensorExactPairing X (𝟙_ C))
  change _ ▷ (X ⊗ (𝟙_ C)) ≫ tensorEvaluation C X (𝟙_ C) =
    _ ▷ (X ⊗ (𝟙_ C)) ≫ tensorEvaluation C X (𝟙_ C)
  simp only [comp_whiskerRight, assoc]
  rw [dualTensorIso_evaluation, rightAdjointMate_comp_evaluation,
    tensorEvaluation_eq, tensorEval_map_rightDual, dualUnitIso_inv_evaluation]
  dsimp [tensorEval]
  monoidal

open Opposite MonoidalOpposite

/-- The chosen right-dual functor, with both variance and tensor order reversed. -/
def rigidDualFunctor : C ⥤ (Cᵒᵖ)ᴹᵒᵖ where
  obj X := mop (op (dual C X))
  map f := (dualMap C f).op.mop
  map_id X := by simp [dualMap]
  map_comp f g := by simp [dualMap, comp_rightAdjointMate]

/-- Right dualization is canonically strong monoidal with the reversed target.
All coherence follows from the actual pairing comparison identities above. -/
def rigidDualCoreMonoidal : (rigidDualFunctor (C := C)).CoreMonoidal where
  εIso := (dualUnitIso (C := C)).op.mop
  μIso X Y := (dualTensorIso X Y).op.mop
  μIso_hom_natural_left f X' := by
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    exact (dualTensorIso_naturality_left f X').symm
  μIso_hom_natural_right X' f := by
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    exact (dualTensorIso_naturality_right X' f).symm
  associativity X Y Z := by
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    simpa [rigidDualFunctor, assoc] using dualTensorIso_associativity X Y Z
  left_unitality X := by
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    dsimp [rigidDualFunctor]
    simp only [assoc]
    change (ρ_ (dual C X)).inv =
      dualMap C (λ_ X).hom ≫ (dualTensorIso (𝟙_ C) X).hom ≫
        dual C X ◁ (dualUnitIso (C := C)).hom
    rw [reassoc_of% dualTensorIso_leftUnitor X, ← whiskerLeft_comp,
      Iso.inv_hom_id, whiskerLeft_id, comp_id]
  right_unitality X := by
    apply Quiver.Hom.unmop_inj
    apply Quiver.Hom.unop_inj
    dsimp [rigidDualFunctor]
    simp only [assoc]
    change (λ_ (dual C X)).inv =
      dualMap C (ρ_ X).hom ≫ (dualTensorIso X (𝟙_ C)).hom ≫
        (dualUnitIso (C := C)).hom ▷ dual C X
    rw [reassoc_of% dualTensorIso_rightUnitor X, ← comp_whiskerRight,
      Iso.inv_hom_id, id_whiskerRight, comp_id]

instance rigidDualMonoidal : (rigidDualFunctor (C := C)).Monoidal :=
  (rigidDualCoreMonoidal (C := C)).toMonoidal

/-- The same chosen duality, with reversed variance and tensor order in the source. -/
def rigidDualBackFunctor : (Cᵒᵖ)ᴹᵒᵖ ⥤ C where
  obj X := dual C (unop (unmop X))
  map f := dualMap C f.unmop.unop
  map_id X := by simp [dualMap]
  map_comp f g := by simp [dualMap, comp_rightAdjointMate]

/-- The reverse-source form of the canonical strong monoidal dual functor. -/
def rigidDualBackCoreMonoidal : (rigidDualBackFunctor (C := C)).CoreMonoidal where
  εIso := (dualUnitIso (C := C)).symm
  μIso X Y := (dualTensorIso (unop (unmop Y)) (unop (unmop X))).symm
  μIso_hom_natural_left {X Y} f X' := by
    dsimp [rigidDualBackFunctor]
    apply (cancel_mono (dualTensorIso (unop (unmop X')) (unop (unmop Y))).hom).1
    simp only [assoc, Iso.inv_hom_id, comp_id]
    rw [dualTensorIso_naturality_right, Iso.inv_hom_id_assoc]
  μIso_hom_natural_right {X Y} X' f := by
    dsimp [rigidDualBackFunctor]
    apply (cancel_mono (dualTensorIso (unop (unmop Y)) (unop (unmop X'))).hom).1
    simp only [assoc, Iso.inv_hom_id, comp_id]
    rw [dualTensorIso_naturality_left, Iso.inv_hom_id_assoc]
  associativity X Y Z := by
    dsimp [rigidDualBackFunctor]
    apply (cancel_mono (dualTensorIso
      (unop (unmop Z) ⊗ unop (unmop Y)) (unop (unmop X))).hom).1
    apply (cancel_mono (dual C (unop (unmop X)) ◁
      (dualTensorIso (unop (unmop Z)) (unop (unmop Y))).hom)).1
    simp only [assoc]
    rw [dualTensorIso_associativity]
    simp only [assoc, Iso.inv_hom_id_assoc, ← comp_whiskerRight_assoc,
      ← whiskerLeft_comp_assoc, ← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id,
      id_whiskerRight, id_comp, comp_id]
  left_unitality X := by
    dsimp [rigidDualBackFunctor]
    have hi : dualMapIso (ρ_ (unop (unmop X))) ≪≫
        dualTensorIso (unop (unmop X)) (𝟙_ C) =
      (λ_ (dual C (unop (unmop X)))).symm ≪≫
        whiskerRightIso (dualUnitIso (C := C)).symm (dual C (unop (unmop X))) :=
      Iso.ext (dualTensorIso_rightUnitor (unop (unmop X)))
    have hh := congrArg Iso.inv hi
    dsimp [dualMapIso] at hh
    rw [hh]
    simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, id_comp]
  right_unitality X := by
    dsimp [rigidDualBackFunctor]
    have hi : dualMapIso (λ_ (unop (unmop X))) ≪≫
        dualTensorIso (𝟙_ C) (unop (unmop X)) =
      (ρ_ (dual C (unop (unmop X)))).symm ≪≫
        whiskerLeftIso (dual C (unop (unmop X))) (dualUnitIso (C := C)).symm :=
      Iso.ext (dualTensorIso_leftUnitor (unop (unmop X)))
    have hh := congrArg Iso.inv hi
    dsimp [dualMapIso] at hh
    rw [hh]
    simp only [← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, id_comp]

instance rigidDualBackMonoidal : (rigidDualBackFunctor (C := C)).Monoidal :=
  (rigidDualBackCoreMonoidal (C := C)).toMonoidal

/-- The canonical strong monoidal structure on double dualization, constructed
from rigidity alone. No pivotal structure is assumed. -/
instance canonicalDoubleDualMonoidal : (doubleDualFunctor C).Monoidal := by
  change (rigidDualFunctor (C := C) ⋙ rigidDualBackFunctor (C := C)).Monoidal
  infer_instance

@[simp] lemma canonicalDoubleDual_unit :
    CategoryTheory.Functor.LaxMonoidal.ε (doubleDualFunctor C) = doubleDualUnitHom C := by
  change (dualUnitIso (C := C)).inv ≫ dualMap C (dualUnitIso (C := C)).hom = _
  simp only [dualUnitIso_inv, dualUnitIso_hom, doubleDualUnitHom]

@[simp] lemma canonicalDoubleDual_tensor (X Y : C) :
    CategoryTheory.Functor.LaxMonoidal.μ (doubleDualFunctor C) X Y =
      doubleDualTensorHom C X Y := by
  change (dualTensorIso (dual C Y) (dual C X)).inv ≫
    dualMap C (dualTensorIso X Y).hom = _
  simp only [dualTensorIso_inv, dualTensorIso_hom, doubleDualTensorHom]

/-- The evaluation/coevaluation definition of a pivotal structure gives an
actual monoidal natural isomorphism for the canonical rigid double-dual functor. -/
instance pivotalHomIsMonoidal (J : PivotalStructure C) : NatTrans.IsMonoidal J.j.hom where
  unit := by
    change 𝟙 _ ≫ J.j.hom.app (𝟙_ C) = _
    rw [id_comp, J.unit, canonicalDoubleDual_unit]
  tensor X Y := by
    change 𝟙 _ ≫ J.j.hom.app (X ⊗ Y) = _
    rw [id_comp, J.tensor, canonicalDoubleDual_tensor]

end Paper18.Category
