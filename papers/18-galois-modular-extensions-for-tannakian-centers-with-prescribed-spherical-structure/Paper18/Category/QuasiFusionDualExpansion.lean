import Paper18.Category.QuasiFusionDualBasic

/-! # The actual finite snake expansions for twisted convolution -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace Paper18.Category.QuasiFusion
variable {A : Type} [Fintype A] [AddGroup A]
open GradedObject.Monoidal
local instance expansionBaseMonoidal : MonoidalCategory (GradedObject A (FGModuleCat ℂ)) :=
  GradedObject.monoidalCategory

def twistedRightSnake (r : A → A → A → ℂˣ) (X : PointedVec A) : X ⟶ X :=
  (λ_ X).inv ≫ twistedCoevaluation r X ▷ X ≫
    (scalarAssociator r X (PointedVec.gradedDual X) X).hom ≫
      X ◁ PointedVec.gradedEvaluation X ≫ (ρ_ X).hom

set_option maxHeartbeats 1000000 in
lemma twistedRightSnake_expansion (r : A → A → A → ℂˣ) (X : PointedVec A) (k : A) :
    twistedRightSnake r X k = (λ_ (X k)).inv ≫ ∑ a, twistedRightSnakeTerm r X a k := by
  change (GradedObject.Monoidal.leftUnitor X).inv k ≫
    GradedObject.Monoidal.whiskerRight (twistedCoevaluation r X) X k ≫
    (scalarAssociator r X (PointedVec.gradedDual X) X).hom k ≫
    GradedObject.Monoidal.whiskerLeft X (PointedVec.gradedEvaluation X) k ≫
    (GradedObject.Monoidal.rightUnitor X).hom k = _
  rw [leftUnitor_inv_apply]
  simp only [assoc]
  rw [ι_tensorHom_assoc, PointedVec.id_apply, MonoidalCategory.tensorHom_id]
  simp only [twistedCoevaluation, PointedVec.mapFromUnit_zero, PointedVec.unitFiberIso]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, Iso.inv_hom_id_assoc]
  simp only [twistedCoevaluationZero, sum_whiskerRight, Preadditive.sum_comp,
    MonoidalLinear.smul_whiskerRight, Linear.smul_comp]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  unfold twistedRightSnakeTerm
  dsimp only [PointedVec.instMonoidalCategory, GradedObject.monoidalCategory]
  rw [← assoc (η_ (X a) (X a)ᘁ) ((X a) ◁ (PointedVec.dualFiberIso X a).inv)
    (ιTensorObj X (PointedVec.gradedDual X) a (-a) 0 (add_neg_cancel a)),
    MonoidalCategory.comp_whiskerRight, assoc,
    ← ιTensorObj₃'_eq_assoc X (PointedVec.gradedDual X) X a (-a) k k (by simp)
      0 (add_neg_cancel a)]

lemma twistedRightSnake_eq_id (r : A → A → A → ℂˣ) (X : PointedVec A) :
    twistedRightSnake r X = 𝟙 X := by
  funext k
  rw [twistedRightSnake_expansion]
  have hs : (∑ a, twistedRightSnakeTerm r X a k) = (λ_ (X k)).hom := by
    rw [Finset.sum_eq_single k]
    · exact twistedRightSnakeTerm_self r X k
    · intro a _ ha
      exact twistedRightSnakeTerm_ne r X a k ha
    · simp
  rw [hs, Iso.inv_hom_id]
  rfl

def twistedLeftSnake (r : A → A → A → ℂˣ) (X : PointedVec A) :
    PointedVec.gradedDual X ⟶ PointedVec.gradedDual X :=
  (ρ_ (PointedVec.gradedDual X)).inv ≫
    (PointedVec.gradedDual X) ◁ twistedCoevaluation r X ≫
    (scalarAssociator r (PointedVec.gradedDual X) X (PointedVec.gradedDual X)).inv ≫
    PointedVec.gradedEvaluation X ▷ PointedVec.gradedDual X ≫
    (λ_ (PointedVec.gradedDual X)).hom

set_option maxHeartbeats 1000000 in
lemma twistedLeftSnake_expansion (r : A → A → A → ℂˣ) (X : PointedVec A) (k : A) :
    twistedLeftSnake r X k = (ρ_ (PointedVec.gradedDual X k)).inv ≫
      ∑ a, twistedLeftSnakeTerm r X a k := by
  change (GradedObject.Monoidal.rightUnitor (PointedVec.gradedDual X)).inv k ≫
    GradedObject.Monoidal.whiskerLeft (PointedVec.gradedDual X) (twistedCoevaluation r X) k ≫
    (scalarAssociator r (PointedVec.gradedDual X) X (PointedVec.gradedDual X)).inv k ≫
    GradedObject.Monoidal.whiskerRight (PointedVec.gradedEvaluation X) (PointedVec.gradedDual X) k ≫
    (GradedObject.Monoidal.leftUnitor (PointedVec.gradedDual X)).hom k = _
  rw [rightUnitor_inv_apply]
  simp only [assoc]
  rw [ι_tensorHom_assoc, PointedVec.id_apply, MonoidalCategory.id_tensorHom]
  simp only [twistedCoevaluation, PointedVec.mapFromUnit_zero, PointedVec.unitFiberIso]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id_assoc]
  simp only [twistedCoevaluationZero, whiskerLeft_sum, Preadditive.sum_comp,
    MonoidalLinear.whiskerLeft_smul, Linear.smul_comp]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  unfold twistedLeftSnakeTerm
  dsimp only [PointedVec.instMonoidalCategory, GradedObject.monoidalCategory]
  rw [← assoc (η_ (X a) (X a)ᘁ) ((X a) ◁ (PointedVec.dualFiberIso X a).inv)
      (ιTensorObj X (PointedVec.gradedDual X) a (-a) 0 (add_neg_cancel a)),
    MonoidalCategory.whiskerLeft_comp]
  simp only [assoc]
  rw [← ιTensorObj₃_eq_assoc (PointedVec.gradedDual X) X (PointedVec.gradedDual X)
    k a (-a) k (by simp [add_assoc]) 0 (add_neg_cancel a)]

lemma twistedLeftSnake_eq_id (r : A → A → A → ℂˣ)
    (hinv : ∀ a, r (-a) a (-a) * r a (-a) a = 1) (X : PointedVec A) :
    twistedLeftSnake r X = 𝟙 (PointedVec.gradedDual X) := by
  funext k
  rw [twistedLeftSnake_expansion]
  have hs : (∑ a, twistedLeftSnakeTerm r X a k) =
      (ρ_ (PointedVec.gradedDual X k)).hom := by
    rw [Finset.sum_eq_single (-k)]
    · exact twistedLeftSnakeTerm_matching r hinv X (-k) k (neg_neg k).symm
    · intro a _ ha
      exact twistedLeftSnakeTerm_ne r X a k ha
    · simp
  rw [hs, Iso.inv_hom_id]
  rfl

end Paper18.Category.QuasiFusion
