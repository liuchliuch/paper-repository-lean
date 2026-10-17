import Paper18.Category.DrinfeldLoopTraceDiagramBasic

/-! # Actual Choi contractions in a pivotal category -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The actual annular Choi endomorphism associated to two rectangular maps. -/
def annularChoi (T A : C) (f : T ⟶ T ⊗ A) (g : T ⊗ A ⟶ T) :
    T ⊗ dual C T ⟶ T ⊗ dual C T :=
  tensorRightHomEquiv T A (dual C A) T g ▷ dual C T ≫
    (α_ T (dual C A) (dual C T)).hom ≫
      T ◁ ((dualTensorIso T A).inv ≫ dualMap C f)

/-- Closing the source rectangle gives an actual map from the unit to `A`. -/
def choiSourceTrace (J : PivotalStructure C) (T A : C) (f : T ⟶ T ⊗ A) :
    𝟙_ C ⟶ A :=
  𝟙 (𝟙_ C) ⊗≫ J.leftCoevaluation T ⊗≫ dual C T ◁ f ⊗≫
    ε_ T (dual C T) ▷ A ⊗≫ 𝟙 A

/-- Closing the target rectangle gives an actual map from `A` to the unit. -/
def choiTargetTrace (J : PivotalStructure C) (T A : C) (g : T ⊗ A ⟶ T) :
    A ⟶ 𝟙_ C :=
  𝟙 A ⊗≫ J.leftCoevaluation T ▷ A ⊗≫ dual C T ◁ g ⊗≫
    ε_ T (dual C T)

/-- The actual cap obtained by closing the dual matrix entry. -/
def choiDualCap (J : PivotalStructure C) (T A : C) (f : T ⟶ T ⊗ A) :
    dual C A ⟶ 𝟙_ C :=
  𝟙 (dual C A) ⊗≫ dual C A ◁ η_ (dual C T) (dual C (dual C T)) ⊗≫
    (dual C A ⊗ dual C T) ◁
      ((show dual C (dual C T) ⟶ T from J.j.inv.app T) ≫ f) ⊗≫
    tensorEvaluation C T A

lemma choiDualCap_eq (J : PivotalStructure C) (T A : C) (f : T ⟶ T ⊗ A) :
    choiDualCap J T A f =
      (ρ_ (dual C A)).inv ≫ dual C A ◁ choiSourceTrace J T A f ≫ ε_ A (dual C A) := by
  dsimp [choiDualCap, choiSourceTrace, tensorEvaluation, PivotalStructure.leftCoevaluation]
  monoidal

/-- Closing the retained dual strand of the actual Choi operator produces
an actual source trace, followed by the target rectangle. -/
lemma rightPartialTrace_annularChoi (J : PivotalStructure C) (T A : C)
    (f : T ⟶ T ⊗ A) (g : T ⊗ A ⟶ T) :
    J.rightPartialTrace (dual C T) (annularChoi T A f g) =
      (ρ_ T).inv ≫ T ◁ choiSourceTrace J T A f ≫ g := by
  let d := tensorRightHomEquiv T A (dual C A) T g
  let h : dual C (dual C T) ⟶ T ⊗ A := J.j.inv.app T ≫ f
  have hc : (dualTensorIso T A).inv ▷ dual C (dual C T) ≫
      dualMap C f ▷ dual C (dual C T) ≫ J.leftEvaluation (dual C T) =
        (dual C A ⊗ dual C T) ◁ h ≫ tensorEvaluation C T A := by
    rw [annularDualMap_cap]
    rw [← assoc, ← whisker_exchange, assoc, dualTensorIso_inv_evaluation]
  have hg : d ▷ A ≫ (α_ T (dual C A) A).hom ≫
      T ◁ ε_ A (dual C A) ≫ (ρ_ T).hom = g :=
    (tensorRightHomEquiv T A (dual C A) T).symm_apply_apply g
  calc
    _ = 𝟙 T ⊗≫ T ◁ η_ (dual C T) (dual C (dual C T)) ⊗≫
        d ▷ (dual C T ⊗ dual C (dual C T)) ⊗≫
        T ◁ ((dualTensorIso T A).inv ▷ dual C (dual C T) ≫
          dualMap C f ▷ dual C (dual C T) ≫ J.leftEvaluation (dual C T)) ⊗≫ 𝟙 T := by
      dsimp only [PivotalStructure.rightPartialTrace, rightClosure, annularChoi, d]
      monoidal
    _ = 𝟙 T ⊗≫ (T ◁ η_ (dual C T) (dual C (dual C T)) ≫
        d ▷ (dual C T ⊗ dual C (dual C T))) ⊗≫
        T ◁ ((dual C A ⊗ dual C T) ◁ h ≫ tensorEvaluation C T A) ⊗≫ 𝟙 T := by
      rw [hc]
      monoidal
    _ = d ≫ T ◁ choiDualCap J T A f ≫ (ρ_ T).hom := by
      rw [whisker_exchange]
      dsimp only [choiDualCap, h]
      monoidal
    _ = 𝟙 T ⊗≫ (d ▷ (𝟙_ C) ≫ (T ⊗ dual C A) ◁ choiSourceTrace J T A f) ⊗≫
        T ◁ ε_ A (dual C A) ⊗≫ 𝟙 T := by
      rw [choiDualCap_eq]
      monoidal
    _ = (ρ_ T).inv ≫ T ◁ choiSourceTrace J T A f ≫
        (d ▷ A ≫ (α_ T (dual C A) A).hom ≫ T ◁ ε_ A (dual C A) ≫ (ρ_ T).hom) := by
      rw [← whisker_exchange]
      monoidal
    _ = _ := by rw [hg]

variable [Preadditive C] [MonoidalPreadditive C]

/-- A vanishing actual unit-Hom space annihilates the annular Choi trace.
The proof already vanishes at the actual partial trace, so sphericality is
not needed. -/
lemma rightTrace_annularChoi_eq_zero (J : PivotalStructure C) (T A : C)
    (hA : ∀ a : 𝟙_ C ⟶ A, a = 0) (f : T ⟶ T ⊗ A) (g : T ⊗ A ⟶ T) :
    J.rightTrace (annularChoi T A f g) = 0 := by
  rw [← J.rightTrace_rightPartialTrace T (dual C T), rightPartialTrace_annularChoi,
    hA (choiSourceTrace J T A f)]
  simp only [MonoidalPreadditive.whiskerLeft_zero, zero_comp, comp_zero, J.rightTrace_zero]

end Paper18.Category.Drinfeld
