import Paper18.Category.DrinfeldLoopTraceDiagramChoi

/-! # Identifying the actual induction annulus with a Choi contraction -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

lemma inductionLoopOpenDiagram_pivotal (J : PivotalStructure C) (T A : C) :
    inductionLoopOpenDiagram J T A =
      𝟙 ((T ⊗ (𝟙_ C)) ⊗ dual C T) ⊗≫
        (T ◁ (η_ A (dual C A) ≫ (ρ_ A).inv ▷ dual C A)) ▷ dual C T ⊗≫
        (((pivotalMap J T ▷ ((A ⊗ (𝟙_ C)) ⊗ dual C A)) ▷ dual C T) ≫
          (dual C (dual C T) ⊗ ((A ⊗ (𝟙_ C)) ⊗ dual C A)) ◁
            pivotalMap J (dual C T)) ⊗≫
        inductionBraidingComparison (𝟙_ C) (dual C T) A := by
  calc
    _ = 𝟙 ((T ⊗ (𝟙_ C)) ⊗ dual C T) ⊗≫
        (T ◁ (η_ A (dual C A) ≫ (ρ_ A).inv ▷ dual C A)) ▷ dual C T ⊗≫
        T ◁ rigidInsertion J (dual C T) ((A ⊗ (𝟙_ C)) ⊗ dual C A) ⊗≫
        (((T ⊗ dual C T) ◁ inductionBraidingComparison (𝟙_ C) (dual C T) A) ≫
          J.leftEvaluation T ▷
            (((dual C (dual C T) ⊗ A) ⊗ (𝟙_ C)) ⊗ dual C (dual C (dual C T) ⊗ A))) ⊗≫
        𝟙 (((dual C (dual C T) ⊗ A) ⊗ (𝟙_ C)) ⊗ dual C (dual C (dual C T) ⊗ A)) := by
      dsimp only [inductionLoopOpenDiagram]
      monoidal
    _ = 𝟙 ((T ⊗ (𝟙_ C)) ⊗ dual C T) ⊗≫
        (T ◁ (η_ A (dual C A) ≫ (ρ_ A).inv ▷ dual C A)) ▷ dual C T ⊗≫
        (𝟙 ((T ⊗ ((A ⊗ (𝟙_ C)) ⊗ dual C A)) ⊗ dual C T) ⊗≫
          T ◁ rigidInsertion J (dual C T) ((A ⊗ (𝟙_ C)) ⊗ dual C A) ⊗≫
          J.leftEvaluation T ▷
            ((dual C (dual C T) ⊗ ((A ⊗ (𝟙_ C)) ⊗ dual C A)) ⊗
              dual C (dual C (dual C T))) ⊗≫
          𝟙 ((dual C (dual C T) ⊗ ((A ⊗ (𝟙_ C)) ⊗ dual C A)) ⊗
              dual C (dual C (dual C T)))) ⊗≫
        inductionBraidingComparison (𝟙_ C) (dual C T) A := by
      rw [whisker_exchange]
      monoidal
    _ = _ := by rw [pivotalInsertionClosure]

lemma inductionLoopAnnularBare_pivotal (J : PivotalStructure C) (T A : C)
    (u : T ⟶ dual C (dual C T) ⊗ A) (p : dual C (dual C T) ⊗ A ⟶ T) :
    inductionLoopAnnularBare J T A u p =
      𝟙 (T ⊗ dual C T) ⊗≫ (T ◁ η_ A (dual C A)) ▷ dual C T ⊗≫
        (((pivotalMap J T ▷ A) ≫ p) ▷ (dual C A ⊗ dual C T)) ⊗≫
        T ◁ ((dual C A ◁ pivotalMap J (dual C T)) ≫
          (dualTensorIso (dual C (dual C T)) A).inv ≫ dualMap C u) := by
  dsimp only [inductionLoopAnnularBare, inductionLoopAnnularTerm]
  rw [inductionLoopOpenDiagram_pivotal]
  calc
    _ = 𝟙 (T ⊗ dual C T) ⊗≫ (T ◁ η_ A (dual C A)) ▷ dual C T ⊗≫
        (pivotalMap J T ▷ A) ▷ (dual C A ⊗ dual C T) ⊗≫
        (((dual C (dual C T) ⊗ A) ◁
          ((dual C A ◁ pivotalMap J (dual C T)) ≫
            (dualTensorIso (dual C (dual C T)) A).inv)) ≫
          p ▷ dual C (dual C (dual C T) ⊗ A)) ⊗≫ T ◁ dualMap C u := by
      dsimp only [inductionBraidingComparison]
      monoidal
    _ = _ := by
      rw [whisker_exchange]
      monoidal

/-- The pivotal comparison on the dual strand is precisely the canonical
dual of the inverse pivotal comparison on the original strand. -/
lemma annularPivotalDualComparison (J : PivotalStructure C) (T A : C) :
    (dual C A ◁ pivotalMap J (dual C T)) ≫
      (dualTensorIso (dual C (dual C T)) A).inv =
    (dualTensorIso T A).inv ≫ dualMap C
      ((show dual C (dual C T) ⟶ T from J.j.inv.app T) ▷ A) := by
  change (dual C A ◁ J.j.hom.app (dual C T)) ≫ _ = _
  rw [J.dual_component]
  apply (cancel_epi (dualTensorIso T A).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← assoc, ← dualTensorIso_naturality_left, assoc]
  change dualMap C (J.j.inv.app T ▷ A) ≫
    (dualTensorIso (dual C (dual C T)) A).hom ≫
      (dualTensorIso (dual C (dual C T)) A).inv = _
  rw [Iso.hom_inv_id, comp_id]

/-- The actual induction-loop annulus is the standard rigid Choi
contraction after the prescribed pivotal change of matrix coordinates. -/
lemma inductionLoopAnnularBare_eq_choi (J : PivotalStructure C) (T A : C)
    (u : T ⟶ dual C (dual C T) ⊗ A) (p : dual C (dual C T) ⊗ A ⟶ T) :
    inductionLoopAnnularBare J T A u p = annularChoi T A
      (u ≫ ((show dual C (dual C T) ⟶ T from J.j.inv.app T) ▷ A))
      ((pivotalMap J T ▷ A) ≫ p) := by
  rw [inductionLoopAnnularBare_pivotal]
  have hd : dualMap C (u ≫ ((show dual C (dual C T) ⟶ T from J.j.inv.app T) ▷ A)) =
      dualMap C ((show dual C (dual C T) ⟶ T from J.j.inv.app T) ▷ A) ≫ dualMap C u :=
    comp_rightAdjointMate
  dsimp only [annularChoi]
  change _ = (((ρ_ T).inv ≫ T ◁ η_ A (dual C A) ≫
    (α_ T A (dual C A)).inv ≫ ((pivotalMap J T ▷ A) ≫ p) ▷ dual C A) ▷ dual C T) ≫
      (α_ T (dual C A) (dual C T)).hom ≫ T ◁
        ((dualTensorIso T A).inv ≫ dualMap C
          (u ≫ ((show dual C (dual C T) ⟶ T from J.j.inv.app T) ▷ A)))
  rw [hd, ← assoc (dualTensorIso T A).inv,
    ← annularPivotalDualComparison J T A]
  monoidal

end Paper18.Category.Drinfeld
