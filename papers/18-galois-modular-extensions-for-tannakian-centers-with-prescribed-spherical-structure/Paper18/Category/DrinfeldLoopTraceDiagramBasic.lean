import Paper18.Category.DrinfeldLoopTraceComponents
import Paper18.Category.PivotalPartialTrace

/-! # Actual annular contractions for the induction-loop trace -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- Removing the coherent middle unit gives an actual tensor endomorphism. -/
def inductionLoopAnnularBare (J : PivotalStructure C) (T A : C)
    (u : T ⟶ dual C (dual C T) ⊗ A) (p : dual C (dual C T) ⊗ A ⟶ T) :
    T ⊗ dual C T ⟶ T ⊗ dual C T :=
  (ρ_ T).inv ▷ dual C T ≫ inductionLoopAnnularTerm J T A u p ≫
    (ρ_ T).hom ▷ dual C T

lemma inductionLoopAnnularBare_trace (J : PivotalStructure C) (T A : C)
    (u : T ⟶ dual C (dual C T) ⊗ A) (p : dual C (dual C T) ⊗ A ⟶ T) :
    J.rightTrace (inductionLoopAnnularBare J T A u p) =
      J.rightTrace (inductionLoopAnnularTerm J T A u p) := by
  unfold inductionLoopAnnularBare
  rw [J.rightTrace_comp]
  simp only [assoc, ← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight, comp_id]

/-- The pivotal cap on the dual strand transfers a dual map to its actual
partner, using the canonical pivotal component. -/
lemma annularDualMap_cap (J : PivotalStructure C) {T K : C} (u : T ⟶ K) :
    dualMap C u ▷ dual C (dual C T) ≫ J.leftEvaluation (dual C T) =
      dual C K ◁ (J.j.inv.app T ≫ u) ≫ ε_ K (dual C K) := by
  dsimp only [PivotalStructure.leftEvaluation]
  rw [J.dual_component]
  simp only [← comp_whiskerRight_assoc]
  rw [← comp_rightAdjointMate]
  exact rightAdjointMate_comp_evaluation _

/-- The actual source-side partial contraction of a matrix entry. -/
def inductionLoopSourceTrace (J : PivotalStructure C) (T A : C)
    (u : T ⟶ dual C (dual C T) ⊗ A) : 𝟙_ C ⟶ A :=
  𝟙 (𝟙_ C) ⊗≫ η_ (dual C T) (dual C (dual C T)) ⊗≫
    dual C T ◁ ((show dual C (dual C T) ⟶ T from J.j.inv.app T) ≫ u) ⊗≫
    J.leftEvaluation (dual C T) ▷ A ⊗≫ 𝟙 A

/-- The actual target-side contraction of the other matrix entry. -/
def inductionLoopTargetTrace (T A : C)
    (p : dual C (dual C T) ⊗ A ⟶ T) : A ⟶ 𝟙_ C :=
  𝟙 A ⊗≫ η_ (dual C T) (dual C (dual C T)) ▷ A ⊗≫
    dual C T ◁ p ⊗≫ ε_ T (dual C T)

end Paper18.Category.Drinfeld
