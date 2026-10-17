import Paper18.Category.DrinfeldSemisimpleBasic

/-! # Duality and trace identities for the actual averaging calculation -/
noncomputable section
universe v u
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Tensor pairing for arbitrary specified exact pairings. -/
def tensorExactPairingSpecified (X Xd Y Yd : C) [ExactPairing X Xd] [ExactPairing Y Yd] :
    ExactPairing (X ⊗ Y) (Yd ⊗ Xd) where
  coevaluation' := 𝟙 (𝟙_ C) ⊗≫ η_ X Xd ⊗≫ X ◁ (η_ Y Yd ▷ Xd) ⊗≫
    𝟙 ((X ⊗ Y) ⊗ (Yd ⊗ Xd))
  evaluation' := 𝟙 ((Yd ⊗ Xd) ⊗ (X ⊗ Y)) ⊗≫ Yd ◁ (ε_ X Xd ▷ Y) ⊗≫ ε_ Y Yd
  evaluation_coevaluation' := by
    calc
      _ = 𝟙 (𝟙_ C ⊗ (X ⊗ Y)) ⊗≫ η_ X Xd ▷ X ▷ Y ⊗≫
          X ◁ (η_ Y Yd ▷ ((Xd ⊗ X) ⊗ Y) ≫
            (Y ⊗ Yd) ◁ (ε_ X Xd ▷ Y)) ⊗≫
          X ◁ Y ◁ ε_ Y Yd ⊗≫ 𝟙 ((X ⊗ Y) ⊗ 𝟙_ C) := by
        monoidal
      _ = 𝟙 (𝟙_ C ⊗ (X ⊗ Y)) ⊗≫
          (η_ X Xd ▷ X ⊗≫ X ◁ ε_ X Xd) ▷ Y ⊗≫
          X ◁ (η_ Y Yd ▷ Y ⊗≫ Y ◁ ε_ Y Yd) ⊗≫
          𝟙 ((X ⊗ Y) ⊗ 𝟙_ C) := by
        rw [← whisker_exchange]
        monoidal
      _ = _ := by
        rw [ExactPairing.evaluation_coevaluation'', ExactPairing.evaluation_coevaluation'']
        monoidal
  coevaluation_evaluation' := by
    calc
      _ = 𝟙 ((Yd ⊗ Xd) ⊗ 𝟙_ C) ⊗≫
          Yd ◁ Xd ◁ η_ X Xd ⊗≫
          Yd ◁ ((Xd ⊗ X) ◁ η_ Y Yd ≫
            ε_ X Xd ▷ (Y ⊗ Yd)) ▷ Xd ⊗≫
          ε_ Y Yd ▷ Yd ▷ Xd ⊗≫ 𝟙 (𝟙_ C ⊗ (Yd ⊗ Xd)) := by
        monoidal
      _ = 𝟙 ((Yd ⊗ Xd) ⊗ 𝟙_ C) ⊗≫
          Yd ◁ (Xd ◁ η_ X Xd ⊗≫ ε_ X Xd ▷ Xd) ⊗≫
          (Yd ◁ η_ Y Yd ⊗≫ ε_ Y Yd ▷ Yd) ▷ Xd ⊗≫
          𝟙 (𝟙_ C ⊗ (Yd ⊗ Xd)) := by
        rw [whisker_exchange]
        monoidal
      _ = _ := by
        rw [ExactPairing.coevaluation_evaluation'', ExactPairing.coevaluation_evaluation'']
        monoidal

/-- With the paired objects fixed, the actual cap determines the cup. -/
lemma exactPairing_coevaluation_eq_of_evaluation_eq {X Y : C}
    (p q : ExactPairing X Y)
    (h : @ExactPairing.evaluation C _ _ X Y p = @ExactPairing.evaluation C _ _ X Y q) :
    @ExactPairing.coevaluation C _ _ X Y p = @ExactPairing.coevaluation C _ _ X Y q := by
  apply (@tensorLeftHomEquiv C _ _ (𝟙_ C) X Y Y q).symm.injective
  change (Y ◁ @ExactPairing.coevaluation C _ _ X Y p ≫ (α_ Y X Y).inv ≫
      @ExactPairing.evaluation C _ _ X Y q ▷ Y ≫ (λ_ Y).hom) =
    (Y ◁ @ExactPairing.coevaluation C _ _ X Y q ≫ (α_ Y X Y).inv ≫
      @ExactPairing.evaluation C _ _ X Y q ▷ Y ≫ (λ_ Y).hom)
  conv_lhs => rw [← h]
  calc
    _ = (Y ◁ @ExactPairing.coevaluation C _ _ X Y p ⊗≫
        @ExactPairing.evaluation C _ _ X Y p ▷ Y) ≫ (λ_ Y).hom := by monoidal
    _ = (Y ◁ @ExactPairing.coevaluation C _ _ X Y q ⊗≫
        @ExactPairing.evaluation C _ _ X Y q ▷ Y) ≫ (λ_ Y).hom := by
      rw [@ExactPairing.coevaluation_evaluation'' C _ _ X Y p,
        @ExactPairing.coevaluation_evaluation'' C _ _ X Y q]
    _ = _ := by monoidal

variable [RightRigidCategory C]

/-- The pivotal left cup of a tensor product is the nested pair of left
cups, under the same canonical anti-tensor comparison as the caps. -/
lemma pivotalLeftCoevaluation_tensor_nested (J : PivotalStructure C) (X Y : C) :
    J.leftCoevaluation (X ⊗ Y) ≫ (dualTensorIso X Y).hom ▷ (X ⊗ Y) =
      𝟙 (𝟙_ C) ⊗≫ J.leftCoevaluation Y ⊗≫
        dual C Y ◁ (J.leftCoevaluation X ▷ Y) ⊗≫
          𝟙 ((dual C Y ⊗ dual C X) ⊗ (X ⊗ Y)) := by
  let p : ExactPairing (dual C Y ⊗ dual C X) (X ⊗ Y) :=
    @tensorExactPairingSpecified C _ _ (dual C Y) Y (dual C X) X
      (J.leftExactPairing Y) (J.leftExactPairing X)
  letI := p
  let q : ExactPairing (dual C (X ⊗ Y)) (X ⊗ Y) :=
    exactPairingCongrLeft (dualTensorIso X Y)
  have he : @ExactPairing.evaluation C _ _ (dual C (X ⊗ Y)) (X ⊗ Y)
      (J.leftExactPairing (X ⊗ Y)) =
      @ExactPairing.evaluation C _ _ (dual C (X ⊗ Y)) (X ⊗ Y) q := by
    change J.leftEvaluation (X ⊗ Y) = (X ⊗ Y) ◁ (dualTensorIso X Y).hom ≫
      @ExactPairing.evaluation C _ _ (dual C Y ⊗ dual C X) (X ⊗ Y) p
    calc
      _ = (X ⊗ Y) ◁ (dualTensorIso X Y).hom ≫
          ((X ⊗ Y) ◁ (dualTensorIso X Y).inv ≫ J.leftEvaluation (X ⊗ Y)) := by
        simp only [← whiskerLeft_comp_assoc, Iso.hom_inv_id, whiskerLeft_id, id_comp]
      _ = _ := by
        rw [pivotalLeftEvaluation_tensor_nested]
        dsimp only [p, tensorExactPairingSpecified, ExactPairing.evaluation,
          PivotalStructure.leftExactPairing_evaluation]
        monoidal
  have hc := exactPairing_coevaluation_eq_of_evaluation_eq
    (J.leftExactPairing (X ⊗ Y)) q he
  change J.leftCoevaluation (X ⊗ Y) =
    @ExactPairing.coevaluation C _ _ (dual C Y ⊗ dual C X) (X ⊗ Y) p ≫
      (dualTensorIso X Y).inv ▷ (X ⊗ Y) at hc
  rw [hc, assoc, ← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight, comp_id]
  dsimp only [p, tensorExactPairingSpecified, ExactPairing.coevaluation,
    PivotalStructure.leftExactPairing_coevaluation]

/-- Closing the first tensor factor by the actual pivotal left trace. -/
def pivotalLeftPartialTrace (J : PivotalStructure C) (X Y : C)
    (f : X ⊗ Y ⟶ X ⊗ Y) : Y ⟶ Y :=
  𝟙 Y ⊗≫ J.leftCoevaluation X ▷ Y ⊗≫ dual C X ◁ f ⊗≫
    ε_ X (dual C X) ▷ Y ⊗≫ 𝟙 Y

/-- Fubini's identity for actual pivotal left traces. -/
lemma pivotalLeftTrace_partial (J : PivotalStructure C) (X Y : C)
    (f : X ⊗ Y ⟶ X ⊗ Y) :
    J.leftTrace (pivotalLeftPartialTrace J X Y f) = J.leftTrace f := by
  have hc : J.leftCoevaluation (X ⊗ Y) =
      (𝟙 (𝟙_ C) ⊗≫ J.leftCoevaluation Y ⊗≫
        dual C Y ◁ (J.leftCoevaluation X ▷ Y) ⊗≫
          𝟙 ((dual C Y ⊗ dual C X) ⊗ (X ⊗ Y))) ≫
            (dualTensorIso X Y).inv ▷ (X ⊗ Y) := by
    rw [← pivotalLeftCoevaluation_tensor_nested, assoc, ← comp_whiskerRight,
      Iso.hom_inv_id, id_whiskerRight, comp_id]
  symm
  dsimp only [PivotalStructure.leftTrace]
  rw [hc]
  calc
    _ = 𝟙 (𝟙_ C) ⊗≫ J.leftCoevaluation Y ⊗≫
        dual C Y ◁ (J.leftCoevaluation X ▷ Y) ⊗≫
        (((dualTensorIso X Y).inv ▷ (X ⊗ Y)) ≫ dual C (X ⊗ Y) ◁ f) ⊗≫
        ε_ (X ⊗ Y) (dual C (X ⊗ Y)) := by monoidal
    _ = 𝟙 (𝟙_ C) ⊗≫ J.leftCoevaluation Y ⊗≫
        dual C Y ◁ (J.leftCoevaluation X ▷ Y) ⊗≫
        (dual C Y ⊗ dual C X) ◁ f ⊗≫
        (((dualTensorIso X Y).inv ▷ (X ⊗ Y)) ≫
          ε_ (X ⊗ Y) (dual C (X ⊗ Y))) := by
      rw [← whisker_exchange]
      monoidal
    _ = _ := by
      rw [dualTensorIso_inv_evaluation]
      dsimp only [pivotalLeftPartialTrace, tensorEvaluation]
      monoidal

lemma pivotalLeftCoevaluation_dual (J : PivotalStructure C) (U : C) :
    J.leftCoevaluation (dual C U) = η_ U (dual C U) ≫ pivotalMap J U ▷ dual C U := by
  have hj : J.j.inv.app (dual C U) = dualMap C (pivotalMap J U) := by
    apply (cancel_epi (J.j.hom.app (dual C U))).mp
    rw [Iso.hom_inv_id_app, J.dual_compatibility]
    rfl
  dsimp only [PivotalStructure.leftCoevaluation]
  rw [hj]
  exact coevaluation_comp_rightAdjointMate _

/-- Rotate a map into the tensor product with a chosen dual. -/
def averagingRotationDown (J : PivotalStructure C) (U A B : C)
    (u : B ⟶ dual C U ⊗ A) : U ⊗ B ⟶ A :=
  U ◁ u ⊗≫ J.leftEvaluation U ▷ A ⊗≫ 𝟙 A

/-- The reverse rotation uses the actual chosen right cup. -/
def averagingRotationUp (U A B : C) (p : dual C U ⊗ A ⟶ B) : A ⟶ U ⊗ B :=
  𝟙 A ⊗≫ η_ U (dual C U) ▷ A ⊗≫ U ◁ p

lemma averagingRotationUp_comp_down (J : PivotalStructure C) (U A B : C)
    (u : B ⟶ dual C U ⊗ A) (p : dual C U ⊗ A ⟶ B) :
    averagingRotationUp U A B p ≫ averagingRotationDown J U A B u =
      pivotalLeftPartialTrace J (dual C U) A (p ≫ u) := by
  symm
  dsimp only [pivotalLeftPartialTrace]
  rw [pivotalLeftCoevaluation_dual]
  calc
    _ = 𝟙 A ⊗≫ η_ U (dual C U) ▷ A ⊗≫
        ((pivotalMap J U ▷ (dual C U ⊗ A)) ≫ dual C (dual C U) ◁ (p ≫ u)) ⊗≫
        ε_ (dual C U) (dual C (dual C U)) ▷ A ⊗≫ 𝟙 A := by monoidal
    _ = _ := by
      rw [← whisker_exchange]
      dsimp only [averagingRotationUp, averagingRotationDown, PivotalStructure.leftEvaluation]
      monoidal

/-- The actual trace pairing is preserved by the rigid rotations used in
the finite semisimple handle-slide calculation. -/
lemma averagingRotation_trace (J : PivotalStructure C) (U A B : C)
    (u : B ⟶ dual C U ⊗ A) (p : dual C U ⊗ A ⟶ B) :
    J.leftTrace (averagingRotationUp U A B p ≫ averagingRotationDown J U A B u) =
      J.leftTrace (u ≫ p) := by
  rw [averagingRotationUp_comp_down, pivotalLeftTrace_partial]
  exact J.leftTrace_comp p u

end Paper18.Category.Drinfeld
