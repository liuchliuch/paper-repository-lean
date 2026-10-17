import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Retract

/-! # Actual right duals of retracts

Split the right mate of the retract idempotent on the original dual. The
resulting pair of retracts carries evaluation and coevaluation obtained
from the original exact pairing.
-/

noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {X Y Z : C} [HasRightDual X] (R : Retract Y X) (T : Retract Z Xᘁ)

/-- Coevaluation restricted to two actual retracts. -/
def retractCoevaluation : 𝟙_ C ⟶ Y ⊗ Z := η_ X Xᘁ ≫ (R.r ⊗ₘ T.r)

/-- Evaluation restricted to two actual retracts. -/
def retractEvaluation : Z ⊗ Y ⟶ 𝟙_ C := (T.i ⊗ₘ R.i) ≫ ε_ X Xᘁ

variable (h : T.r ≫ T.i = (R.r ≫ R.i)ᘁ)
include h

/-- The projection onto the dual retract is compatible with evaluation. -/
lemma retractEvaluation_projection :
    T.r ▷ Y ≫ retractEvaluation R T = Xᘁ ◁ R.i ≫ ε_ X Xᘁ := by
  unfold retractEvaluation
  rw [tensorHom_def]
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc, h, ← whisker_exchange_assoc,
    rightAdjointMate_comp_evaluation, ← whiskerLeft_comp_assoc]
  simp only [← Category.assoc, R.retract, Category.id_comp]

/-- The inclusion of the first retract is compatible with coevaluation. -/
lemma retractCoevaluation_inclusion :
    retractCoevaluation R T ≫ R.i ▷ Z = η_ X Xᘁ ≫ X ◁ T.r := by
  unfold retractCoevaluation
  rw [tensorHom_def]
  simp only [Category.assoc]
  rw [whisker_exchange, ← comp_whiskerRight_assoc,
    ← coevaluation_comp_rightAdjointMate_assoc, ← h, ← whiskerLeft_comp]
  simp only [Category.assoc, T.retract, Category.comp_id]

/-- Compatible splitting of a retract idempotent and its mate gives an actual
exact pairing on the two retract objects. -/
def retractExactPairing : ExactPairing Y Z where
  coevaluation' := retractCoevaluation R T
  evaluation' := retractEvaluation R T
  evaluation_coevaluation' := by
    calc
      _ = η_ X Xᘁ ▷ Y ⊗≫
          (R.r ▷ (Xᘁ ⊗ Y) ≫ Y ◁ (T.r ▷ Y ≫ retractEvaluation R T)) := by
        dsimp [retractCoevaluation]
        rw [tensorHom_def]
        monoidal
      _ = η_ X Xᘁ ▷ Y ⊗≫
          (R.r ▷ (Xᘁ ⊗ Y) ≫ Y ◁ (Xᘁ ◁ R.i ≫ ε_ X Xᘁ)) := by
        rw [retractEvaluation_projection R T h]
      _ = η_ X Xᘁ ▷ Y ⊗≫ X ◁ (Xᘁ ◁ R.i ≫ ε_ X Xᘁ) ⊗≫
          R.r ⊗≫ 𝟙 (Y ⊗ 𝟙_ C) := by
        rw [← whisker_exchange]
        monoidal
      _ = 𝟙 _ ⊗≫ (η_ X Xᘁ ▷ Y ≫ (X ⊗ Xᘁ) ◁ R.i) ⊗≫
          X ◁ ε_ X Xᘁ ⊗≫ R.r ⊗≫ 𝟙 _ := by monoidal
      _ = 𝟙 _ ⊗≫ R.i ⊗≫ (η_ X Xᘁ ▷ X ⊗≫ X ◁ ε_ X Xᘁ) ⊗≫
          R.r ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
        monoidal
      _ = 𝟙 _ ⊗≫ (R.i ≫ R.r) ⊗≫ 𝟙 _ := by
        rw [ExactPairing.evaluation_coevaluation'']
        monoidal
      _ = _ := by rw [R.retract]; monoidal
  coevaluation_evaluation' := by
    calc
      _ = Z ◁ (retractCoevaluation R T ≫ R.i ▷ Z) ⊗≫
          T.i ▷ (X ⊗ Z) ⊗≫ ε_ X Xᘁ ▷ Z := by
        dsimp [retractEvaluation]
        rw [tensorHom_def']
        monoidal
      _ = Z ◁ (η_ X Xᘁ ≫ X ◁ T.r) ⊗≫
          T.i ▷ (X ⊗ Z) ⊗≫ ε_ X Xᘁ ▷ Z := by
        rw [retractCoevaluation_inclusion R T h]
      _ = (Z ◁ η_ X Xᘁ ≫
          (Z ◁ (X ◁ T.r) ≫ T.i ▷ (X ⊗ Z))) ⊗≫ ε_ X Xᘁ ▷ Z := by monoidal
      _ = (Z ◁ η_ X Xᘁ ≫
          (T.i ▷ (X ⊗ Xᘁ) ≫ Xᘁ ◁ (X ◁ T.r))) ⊗≫ ε_ X Xᘁ ▷ Z := by
        rw [whisker_exchange]
      _ = 𝟙 _ ⊗≫ (Z ◁ η_ X Xᘁ ≫ T.i ▷ (X ⊗ Xᘁ)) ⊗≫
          ((Xᘁ ⊗ X) ◁ T.r ≫ ε_ X Xᘁ ▷ Z) ⊗≫ 𝟙 _ := by monoidal
      _ = 𝟙 _ ⊗≫ T.i ⊗≫ (Xᘁ ◁ η_ X Xᘁ ⊗≫ ε_ X Xᘁ ▷ Xᘁ) ⊗≫
          T.r ⊗≫ 𝟙 _ := by
        rw [whisker_exchange, whisker_exchange]
        monoidal
      _ = 𝟙 _ ⊗≫ (T.i ≫ T.r) ⊗≫ 𝟙 _ := by
        rw [ExactPairing.coevaluation_evaluation'']
        monoidal
      _ = _ := by rw [T.retract]; monoidal

omit h T in
/-- In an idempotent-complete monoidal category, a retract of an object with a
right dual has an actual chosen right dual. The dual object is obtained by
splitting the mate idempotent on the original dual. -/
def hasRightDualOfRetract [IsIdempotentComplete C] : HasRightDual Y := by
  let e : Xᘁ ⟶ Xᘁ := (R.r ≫ R.i)ᘁ
  have he : e ≫ e = e := by
    dsimp [e]
    rw [← comp_rightAdjointMate]
    congr 1
    simp only [Category.assoc, R.retract_assoc]
  have hs := IsIdempotentComplete.idempotents_split Xᘁ e he
  let W := Classical.choose hs
  let i := Classical.choose (Classical.choose_spec hs)
  let p := Classical.choose (Classical.choose_spec (Classical.choose_spec hs))
  have hip : i ≫ p = 𝟙 W ∧ p ≫ i = e :=
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hs))
  exact { rightDual := W
          exact := retractExactPairing R { i := i, r := p, retract := hip.1 } hip.2 }

section Kernels
variable [Preadditive C] [CategoryTheory.Limits.HasKernels C]

omit h T R in
/-- Actual kernels split every idempotent in a preadditive category. -/
def idempotentCompleteOfKernels : IsIdempotentComplete C :=
  (Idempotents.isIdempotentComplete_iff_idempotents_have_kernels C).mpr
    (fun _ _ _ => inferInstance)

omit h T in
/-- The kernel-based form of retract closure of actual right duals. -/
def hasRightDualOfRetractOfKernels : HasRightDual Y := by
  letI := idempotentCompleteOfKernels (C := C)
  exact hasRightDualOfRetract R

end Kernels

end Paper18.Category
