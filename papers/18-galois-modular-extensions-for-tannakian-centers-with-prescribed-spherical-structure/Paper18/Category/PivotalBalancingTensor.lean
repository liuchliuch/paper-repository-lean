import Paper18.Category.PivotalBalancingBasic
import Paper18.Category.Braided

noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
universe v u
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]

/-- The four-strand rearrangement used when comparing the swapped tensor
pairing with the tensor product of swapped pairings. -/
lemma balancing_four_braid (X Y P Q : C) :
    (doubleBraiding X Y).hom ▷ (P ⊗ Q) ≫ (β_ (X ⊗ Y) (P ⊗ Q)).hom =
      𝟙 ((X ⊗ Y) ⊗ (P ⊗ Q)) ⊗≫ (β_ X (Y ⊗ P)).hom ▷ Q ⊗≫
      (Y ⊗ P) ◁ (β_ X Q).hom ⊗≫ (β_ Y P).hom ▷ (Q ⊗ X) ⊗≫
      P ◁ (β_ Y (Q ⊗ X)).hom ⊗≫ 𝟙 ((P ⊗ Q) ⊗ (X ⊗ Y)) := by
  calc
    _ = 𝟙 ((X ⊗ Y) ⊗ (P ⊗ Q)) ⊗≫ (β_ X Y).hom ▷ (P ⊗ Q) ⊗≫
        ((β_ Y X).hom ▷ P ⊗≫ X ◁ (β_ Y P).hom ⊗≫ (β_ X P).hom ▷ Y) ▷ Q ⊗≫
        P ◁ X ◁ (β_ Y Q).hom ⊗≫ P ◁ (β_ X Q).hom ▷ Y ⊗≫
        𝟙 ((P ⊗ Q) ⊗ (X ⊗ Y)) := by
      simp only [doubleBraiding, Iso.trans_hom, comp_whiskerRight,
        braiding_tensor_left_hom, braiding_tensor_right_hom]
      monoidal
    _ = 𝟙 ((X ⊗ Y) ⊗ (P ⊗ Q)) ⊗≫ (β_ X Y).hom ▷ (P ⊗ Q) ⊗≫
        (𝟙 _ ⊗≫ (Y ◁ (β_ X P).hom ⊗≫ (β_ Y P).hom ▷ X ⊗≫
          P ◁ (β_ Y X).hom) ⊗≫ 𝟙 _) ▷ Q ⊗≫
        P ◁ X ◁ (β_ Y Q).hom ⊗≫ P ◁ (β_ X Q).hom ▷ Y ⊗≫
        𝟙 ((P ⊗ Q) ⊗ (X ⊗ Y)) := by rw [yang_baxter']
    _ = 𝟙 ((X ⊗ Y) ⊗ (P ⊗ Q)) ⊗≫ (β_ X Y).hom ▷ (P ⊗ Q) ⊗≫
        Y ◁ (β_ X P).hom ▷ Q ⊗≫ (β_ Y P).hom ▷ (X ⊗ Q) ⊗≫
        P ◁ ((β_ Y X).hom ▷ Q ⊗≫ X ◁ (β_ Y Q).hom ⊗≫ (β_ X Q).hom ▷ Y) ⊗≫
        𝟙 ((P ⊗ Q) ⊗ (X ⊗ Y)) := by monoidal
    _ = 𝟙 ((X ⊗ Y) ⊗ (P ⊗ Q)) ⊗≫ (β_ X Y).hom ▷ (P ⊗ Q) ⊗≫
        Y ◁ (β_ X P).hom ▷ Q ⊗≫ (β_ Y P).hom ▷ (X ⊗ Q) ⊗≫
        P ◁ (𝟙 _ ⊗≫ (Y ◁ (β_ X Q).hom ⊗≫ (β_ Y Q).hom ▷ X ⊗≫
          Q ◁ (β_ Y X).hom) ⊗≫ 𝟙 _) ⊗≫
        𝟙 ((P ⊗ Q) ⊗ (X ⊗ Y)) := by rw [yang_baxter']
    _ = 𝟙 ((X ⊗ Y) ⊗ (P ⊗ Q)) ⊗≫ (β_ X (Y ⊗ P)).hom ▷ Q ⊗≫
        ((β_ Y P).hom ▷ (X ⊗ Q) ≫ (P ⊗ Y) ◁ (β_ X Q).hom) ⊗≫
        P ◁ (β_ Y (Q ⊗ X)).hom ⊗≫ 𝟙 ((P ⊗ Q) ⊗ (X ⊗ Y)) := by
      simp only [braiding_tensor_right_hom]
      monoidal
    _ = _ := by
      rw [← whisker_exchange]
      monoidal


/-- The swapped tensor cap differs from the tensor of the swapped caps by
the double braiding. This is a pure braiding/evaluation identity. -/
lemma balancing_tensor_eval (X Y P Q : C)
    (ex : Q ⊗ X ⟶ 𝟙_ C) (ey : P ⊗ Y ⟶ 𝟙_ C) :
    (doubleBraiding X Y).hom ▷ (P ⊗ Q) ≫
        (β_ (X ⊗ Y) (P ⊗ Q)).hom ≫ tensorEval X Y Q P ex ey =
      tensorEval P Q Y X ((β_ Y P).hom ≫ ey) ((β_ X Q).hom ≫ ex) := by
  let lx := (β_ X Q).hom ≫ ex
  let ly := (β_ Y P).hom ≫ ey
  rw [← assoc, balancing_four_braid]
  calc
    _ = 𝟙 ((X ⊗ Y) ⊗ (P ⊗ Q)) ⊗≫ (β_ X (Y ⊗ P)).hom ▷ Q ⊗≫
        (Y ⊗ P) ◁ (β_ X Q).hom ⊗≫ (β_ Y P).hom ▷ (Q ⊗ X) ⊗≫
        P ◁ ((β_ Y (Q ⊗ X)).hom ≫ ex ▷ Y) ⊗≫ ey ⊗≫ 𝟙 (𝟙_ C) := by
      dsimp [tensorEval]
      monoidal
    _ = 𝟙 ((X ⊗ Y) ⊗ (P ⊗ Q)) ⊗≫ (β_ X (Y ⊗ P)).hom ▷ Q ⊗≫
        (Y ⊗ P) ◁ (β_ X Q).hom ⊗≫ (β_ Y P).hom ▷ (Q ⊗ X) ⊗≫
        P ◁ (Y ◁ ex ≫ (β_ Y (𝟙_ C)).hom) ⊗≫ ey ⊗≫ 𝟙 (𝟙_ C) := by
      rw [← braiding_naturality_right]
    _ = 𝟙 ((X ⊗ Y) ⊗ (P ⊗ Q)) ⊗≫ (β_ X (Y ⊗ P)).hom ▷ Q ⊗≫
        (Y ⊗ P) ◁ (β_ X Q).hom ⊗≫
        ((β_ Y P).hom ▷ (Q ⊗ X) ≫ (P ⊗ Y) ◁ ex) ⊗≫ ey ⊗≫ 𝟙 (𝟙_ C) := by
      simp only [braiding_tensorUnit_right]
      monoidal
    _ = 𝟙 ((X ⊗ Y) ⊗ (P ⊗ Q)) ⊗≫ (β_ X (Y ⊗ P)).hom ▷ Q ⊗≫
        (Y ⊗ P) ◁ (β_ X Q).hom ⊗≫
        ((Y ⊗ P) ◁ ex ≫ (β_ Y P).hom ▷ (𝟙_ C)) ⊗≫ ey ⊗≫ 𝟙 (𝟙_ C) := by
      rw [← whisker_exchange]
    _ = 𝟙 ((X ⊗ Y) ⊗ (P ⊗ Q)) ⊗≫ (β_ X (Y ⊗ P)).hom ▷ Q ⊗≫
        ((Y ⊗ P) ◁ lx ≫ ly ▷ (𝟙_ C)) ⊗≫ 𝟙 (𝟙_ C) := by
      dsimp [lx, ly]
      monoidal
    _ = 𝟙 ((X ⊗ Y) ⊗ (P ⊗ Q)) ⊗≫
        ((β_ X (Y ⊗ P)).hom ≫ ly ▷ X) ▷ Q ⊗≫ lx ⊗≫ 𝟙 (𝟙_ C) := by
      rw [whisker_exchange]
      monoidal
    _ = 𝟙 ((X ⊗ Y) ⊗ (P ⊗ Q)) ⊗≫
        (X ◁ ly ≫ (β_ X (𝟙_ C)).hom) ▷ Q ⊗≫ lx ⊗≫ 𝟙 (𝟙_ C) := by
      rw [← braiding_naturality_right]
    _ = _ := by
      dsimp [tensorEval, lx, ly]
      simp only [braiding_tensorUnit_right]
      monoidal

/-- Pairing the canonical double-dual tensorator agrees with the tensor cap
under the canonical chosen-dual comparison. -/
lemma doubleDualTensor_pairing (X Y : C)
    (f : X ⊗ Y ⟶ (doubleDualFunctor C).obj X ⊗ (doubleDualFunctor C).obj Y) :
    (X ⊗ Y) ◁ (dualTensorIso X Y).inv ≫
        (f ≫ doubleDualTensorHom C X Y) ▷ dual C (X ⊗ Y) ≫
        ε_ (dual C (X ⊗ Y)) (dual C (dual C (X ⊗ Y))) =
      f ▷ (dual C Y ⊗ dual C X) ≫ tensorEvaluation C (dual C Y) (dual C X) := by
  simp only [doubleDualTensorHom, comp_whiskerRight, assoc]
  rw [rightAdjointMate_comp_evaluation (dualTensorTo C X Y)]
  rw [whisker_exchange_assoc, whisker_exchange_assoc]
  simp only [← whiskerLeft_comp_assoc, ← dualTensorIso_hom,
    Iso.inv_hom_id, whiskerLeft_id, id_comp]
  rw [← dualTensorIso_inv, dualTensorIso_inv_evaluation]

/-- The two Drinfeld comparisons turn the tensor cap into the two braided caps. -/
lemma drinfeld_tensor_pairing (X Y : C) :
    ((drinfeldIso X).hom ⊗ₘ (drinfeldIso Y).hom) ▷ (dual C Y ⊗ dual C X) ≫
        tensorEvaluation C (dual C Y) (dual C X) =
      (doubleBraiding X Y).hom ▷ (dual C Y ⊗ dual C X) ≫
        (β_ (X ⊗ Y) (dual C Y ⊗ dual C X)).hom ≫ tensorEvaluation C X Y := by
  simp only [tensorEvaluation_eq]
  rw [balancing_tensor_eval]
  rw [tensorHom_def, comp_whiskerRight, assoc]
  dsimp only [doubleDualFunctor]
  rw [tensorEval_map_leftDual, tensorEval_map_rightDual,
    drinfeldIso_evaluation, drinfeldIso_evaluation]

/-- The tensor defect of the actual Drinfeld comparison is precisely the
inverse monodromy, proved from actual pairing uniqueness and the hexagons. -/
lemma drinfeldIso_tensor (X Y : C) :
    (doubleBraiding X Y).hom ≫ (drinfeldIso (X ⊗ Y)).hom =
      ((drinfeldIso X).hom ⊗ₘ (drinfeldIso Y).hom) ≫ doubleDualTensorHom C X Y := by
  apply pairing_hom_ext
    (inferInstanceAs (ExactPairing (dual C (X ⊗ Y)) (dual C (dual C (X ⊗ Y)))))
  apply (cancel_epi ((X ⊗ Y) ◁ (dualTensorIso X Y).inv)).1
  rw [doubleDualTensor_pairing]
  simp only [comp_whiskerRight, assoc]
  rw [drinfeldIso_evaluation, whisker_exchange_assoc,
    braiding_naturality_right_assoc, dualTensorIso_inv_evaluation]
  exact (drinfeld_tensor_pairing X Y).symm

/-- The Drinfeld comparison has the canonical rigid unit component. -/
lemma drinfeldIso_unit : (drinfeldIso (𝟙_ C)).hom = doubleDualUnitHom C := by
  apply pairing_hom_ext
    (inferInstanceAs (ExactPairing (dual C (𝟙_ C)) (dual C (dual C (𝟙_ C)))))
  rw [drinfeldIso_evaluation]
  simp only [doubleDualUnitHom, comp_whiskerRight, assoc]
  rw [rightAdjointMate_comp_evaluation (dualUnitTo C), ← whisker_exchange_assoc]
  rw [← dualUnitIso_evaluation]
  simp only [dualUnitIso_hom, ← comp_whiskerRight_assoc,
    ← dualUnitIso_hom, ← dualUnitIso_inv, Iso.inv_hom_id,
    id_whiskerRight, id_comp]
  rw [← braiding_naturality_right_assoc]
  simp only [braiding_tensorUnit_left, assoc]
  monoidal

end Paper18.Category
