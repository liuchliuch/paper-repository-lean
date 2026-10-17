import Paper18.Category.DrinfeldInductionBraiding

/-! # Naturality of the actual central-induction commutation maps -/
noncomputable section
universe v u w
namespace Paper18.Category.Drinfeld
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
attribute [local instance 2000] RightRigidCategory.rightDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

lemma dualTensorIso_inv_naturality_left {D E : C} (f : D ⟶ E) (T : C) :
    (dual C T ◁ dualMap C f) ≫ (dualTensorIso D T).inv =
      (dualTensorIso E T).inv ≫ dualMap C (f ▷ T) := by
  apply (cancel_epi (dualTensorIso E T).hom).mp
  rw [← assoc, ← dualTensorIso_naturality_left]
  simp only [assoc, Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc]

/-- The cup and the final pivotal component may be indexed separately. -/
def mixedRigidInsertion (J : PivotalStructure C) (U V A : C) :
    A ⊗ U ⟶ V ⊗ ((dual C V ⊗ A) ⊗ dual C (dual C U)) :=
  𝟙 (A ⊗ U) ⊗≫ η_ V (dual C V) ▷ (A ⊗ U) ⊗≫
    (V ⊗ (dual C V ⊗ A)) ◁ pivotalMap J U ⊗≫
      𝟙 (V ⊗ ((dual C V ⊗ A) ⊗ dual C (dual C U)))

@[reassoc]
lemma rigidInsertion_input_naturality (J : PivotalStructure C) (A : C)
    {U V : C} (f : U ⟶ V) :
    (A ◁ f) ≫ rigidInsertion J V A =
      mixedRigidInsertion J U V A ≫
        V ◁ ((dual C V ⊗ A) ◁ dualMap C (dualMap C f)) := by
  have hn : f ≫ pivotalMap J V = pivotalMap J U ≫ dualMap C (dualMap C f) :=
    J.j.hom.naturality f
  calc
    _ = 𝟙 (A ⊗ U) ⊗≫
        ((𝟙_ C) ◁ (A ◁ f) ≫ η_ V (dual C V) ▷ (A ⊗ V)) ⊗≫
        (V ⊗ (dual C V ⊗ A)) ◁ pivotalMap J V ⊗≫
          𝟙 (V ⊗ ((dual C V ⊗ A) ⊗ dual C (dual C V))) := by
      dsimp [rigidInsertion]
      monoidal
    _ = 𝟙 (A ⊗ U) ⊗≫ η_ V (dual C V) ▷ (A ⊗ U) ⊗≫
        (V ⊗ (dual C V ⊗ A)) ◁ (f ≫ pivotalMap J V) ⊗≫
          𝟙 (V ⊗ ((dual C V ⊗ A) ⊗ dual C (dual C V))) := by
      rw [whisker_exchange]
      monoidal
    _ = _ := by
      rw [hn]
      dsimp [mixedRigidInsertion]
      monoidal

@[reassoc]
lemma rigidInsertion_output_naturality (J : PivotalStructure C) (A : C)
    {U V : C} (f : U ⟶ V) :
    rigidInsertion J U A ≫ (f ▷ ((dual C U ⊗ A) ⊗ dual C (dual C U))) =
      mixedRigidInsertion J U V A ≫
        V ◁ ((dualMap C f ▷ A) ▷ dual C (dual C U)) := by
  calc
    _ = 𝟙 (A ⊗ U) ⊗≫ η_ U (dual C U) ▷ (A ⊗ U) ⊗≫
        (((U ⊗ (dual C U ⊗ A)) ◁ pivotalMap J U) ≫
          (f ▷ (dual C U ⊗ A)) ▷ dual C (dual C U)) ⊗≫
          𝟙 (V ⊗ ((dual C U ⊗ A) ⊗ dual C (dual C U))) := by
      dsimp [rigidInsertion]
      monoidal
    _ = 𝟙 (A ⊗ U) ⊗≫
        (η_ U (dual C U) ≫ f ▷ dual C U) ▷ (A ⊗ U) ⊗≫
        (V ⊗ (dual C U ⊗ A)) ◁ pivotalMap J U ⊗≫
          𝟙 (V ⊗ ((dual C U ⊗ A) ⊗ dual C (dual C U))) := by
      rw [whisker_exchange]
      monoidal
    _ = 𝟙 (A ⊗ U) ⊗≫ η_ V (dual C V) ▷ (A ⊗ U) ⊗≫
        (((V ◁ (dualMap C f ▷ A)) ▷ U) ≫
          (V ⊗ (dual C U ⊗ A)) ◁ pivotalMap J U) ⊗≫
          𝟙 (V ⊗ ((dual C U ⊗ A) ⊗ dual C (dual C U))) := by
      rw [← coevaluation_comp_rightAdjointMate f]
      monoidal
    _ = _ := by
      rw [← whisker_exchange]
      dsimp [mixedRigidInsertion]
      monoidal

section Coend
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- The tail absorbs the contravariant dual map on the indexing strand and
its double-dual mate on the final strand by the actual coend relation. -/
lemma inductionBraidingTail_naturality (X T : C) {U V : C} (f : U ⟶ V) :
    ((dual C V ⊗ ((T ⊗ X) ⊗ dual C T)) ◁ dualMap C (dualMap C f)) ≫
      inductionBraidingTail S X V T =
    (dualMap C f ▷ ((T ⊗ X) ⊗ dual C T)) ▷ dual C (dual C U) ≫
      inductionBraidingTail S X U T := by
  calc
    _ = 𝟙 ((dual C V ⊗ ((T ⊗ X) ⊗ dual C T)) ⊗ dual C (dual C U)) ⊗≫
        (((dual C V ⊗ T) ⊗ X) ◁
          ((dual C T ◁ dualMap C (dualMap C f)) ≫ (dualTensorIso (dual C V) T).inv)) ⊗≫
        inductionι S X (dual C V ⊗ T) := by
      dsimp [inductionBraidingTail]
      monoidal
    _ = 𝟙 ((dual C V ⊗ ((T ⊗ X) ⊗ dual C T)) ⊗ dual C (dual C U)) ⊗≫
        (((dual C V ⊗ T) ⊗ X) ◁ (dualTensorIso (dual C U) T).inv) ⊗≫
        ((((dual C V ⊗ T) ⊗ X) ◁ dualMap C (dualMap C f ▷ T)) ≫
          inductionι S X (dual C V ⊗ T)) := by
      rw [dualTensorIso_inv_naturality_left]
      monoidal
    _ = _ := by
      rw [inductionι_dinatural]
      calc
        _ = 𝟙 ((dual C V ⊗ ((T ⊗ X) ⊗ dual C T)) ⊗ dual C (dual C U)) ⊗≫
            ((((dual C V ⊗ T) ⊗ X) ◁ (dualTensorIso (dual C U) T).inv) ≫
              (((dualMap C f ▷ T) ▷ X) ▷ (dual C U ⊗ T)ᘁ)) ⊗≫
            inductionι S X (dual C U ⊗ T) := by monoidal
        _ = _ := by
          rw [whisker_exchange]
          dsimp [inductionBraidingTail]
          monoidal

/-- Naturality in the crossed object of the universal components. -/
lemma inductionHalfBraidingComponent_naturality (J : PivotalStructure C) (X T : C)
    {U V : C} (f : U ⟶ V) :
    (((T ⊗ X) ⊗ dual C T) ◁ f) ≫ inductionHalfBraidingComponent S J X V T =
      inductionHalfBraidingComponent S J X U T ≫ (f ▷ inductionUnderlying S X) := by
  unfold inductionHalfBraidingComponent
  rw [← assoc, rigidInsertion_input_naturality, assoc, ← whiskerLeft_comp,
    inductionBraidingTail_naturality, whiskerLeft_comp, ← assoc,
    ← rigidInsertion_output_naturality, assoc, ← whisker_exchange]
  rw [assoc]

/-- The coend commutation maps are natural in the actual crossed object. -/
lemma inductionHalfBraidingHom_naturality (J : PivotalStructure C) (X : C)
    {U V : C} (f : U ⟶ V) :
    (inductionUnderlying S X ◁ f) ≫ inductionHalfBraidingHom S J X V =
      inductionHalfBraidingHom S J X U ≫ (f ▷ inductionUnderlying S X) := by
  letI := inductionHasCoend S X
  apply mappedCoend_hom_ext (inductionDiagram X) (tensorRight U)
  intro T
  change (inductionι S X T ▷ U) ≫ _ = (inductionι S X T ▷ U) ≫ _
  rw [← whisker_exchange_assoc, inductionHalfBraidingHom_ι,
    ← assoc, inductionHalfBraidingHom_ι]
  exact inductionHalfBraidingComponent_naturality S J X T f

end Coend
end Paper18.Category.Drinfeld
