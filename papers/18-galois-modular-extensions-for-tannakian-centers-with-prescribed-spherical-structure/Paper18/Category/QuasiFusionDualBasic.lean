import Paper18.Category.QuasiFusionLinear
import Paper18.Category.PointedRigid

/-! # Actual weighted cups for twisted graded convolution -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace Paper18.Category.QuasiFusion
variable {A : Type} [Fintype A] [AddGroup A]
open GradedObject.Monoidal
local instance dualBaseMonoidal : MonoidalCategory (GradedObject A (FGModuleCat ℂ)) :=
  GradedObject.monoidalCategory

def cupWeight (r : A → A → A → ℂˣ) (a : A) : ℂ := ((r a (-a) a)⁻¹ : ℂˣ)

/-- The actual weighted finite sum of homogeneous vector-space cups. -/
def twistedCoevaluationZero (r : A → A → A → ℂˣ) (X : PointedVec A) :
    𝟙_ (FGModuleCat ℂ) ⟶ (X ⊗ PointedVec.gradedDual X) 0 :=
  ∑ a, cupWeight r a •
    (η_ (X a) (X a)ᘁ ≫ (X a) ◁ (PointedVec.dualFiberIso X a).inv ≫
      ιTensorObj X (PointedVec.gradedDual X) a (-a) 0 (add_neg_cancel a))

/-- The actual graded cup, with inverse associator weight on every degree. -/
def twistedCoevaluation (r : A → A → A → ℂˣ) (X : PointedVec A) :
    𝟙_ (PointedVec A) ⟶ X ⊗ PointedVec.gradedDual X :=
  PointedVec.mapFromUnit (twistedCoevaluationZero r X)

lemma baseRightSnakeTerm_shape (X : PointedVec A) (a k : A) :
    PointedVec.rightSnakeTerm X a k =
      (η_ (X a) (X a)ᘁ ≫ (X a) ◁ (PointedVec.dualFiberIso X a).inv) ▷ X k ≫
      ιTensorObj₃' X (PointedVec.gradedDual X) X a (-a) k k (by simp) ≫
      (GradedObject.Monoidal.associator X (PointedVec.gradedDual X) X).hom k ≫
      GradedObject.Monoidal.whiskerLeft X (PointedVec.gradedEvaluation X) k ≫
      (GradedObject.Monoidal.rightUnitor X).hom k := by
  unfold PointedVec.rightSnakeTerm
  rw [← assoc (η_ (X a) (X a)ᘁ) ((X a) ◁ (PointedVec.dualFiberIso X a).inv)
    (ιTensorObj X (PointedVec.gradedDual X) a (-a) 0 (add_neg_cancel a)),
    MonoidalCategory.comp_whiskerRight, assoc,
    ← ιTensorObj₃'_eq_assoc X (PointedVec.gradedDual X) X a (-a) k k (by simp)
      0 (add_neg_cancel a)]

def twistedRightSnakeTerm (r : A → A → A → ℂˣ) (X : PointedVec A) (a k : A) :
    𝟙_ (FGModuleCat ℂ) ⊗ X k ⟶ X k :=
  cupWeight r a •
    ((η_ (X a) (X a)ᘁ ≫ (X a) ◁ (PointedVec.dualFiberIso X a).inv) ▷ X k ≫
      ιTensorObj₃' X (PointedVec.gradedDual X) X a (-a) k k (by simp) ≫
      (scalarAssociator r X (PointedVec.gradedDual X) X).hom k ≫
      GradedObject.Monoidal.whiskerLeft X (PointedVec.gradedEvaluation X) k ≫
      (GradedObject.Monoidal.rightUnitor X).hom k)

lemma twistedRightSnakeTerm_eq (r : A → A → A → ℂˣ) (X : PointedVec A) (a k : A) :
    twistedRightSnakeTerm r X a k =
      (cupWeight r a * (r a (-a) k : ℂ)) • PointedVec.rightSnakeTerm X a k := by
  have hh : ιTensorObj₃' X (PointedVec.gradedDual X) X a (-a) k k (by simp) ≫
      (scalarAssociator r X (PointedVec.gradedDual X) X).hom k =
    (r a (-a) k : ℂ) •
      (ιTensorObj₃' X (PointedVec.gradedDual X) X a (-a) k k (by simp) ≫
        (GradedObject.Monoidal.associator X (PointedVec.gradedDual X) X).hom k) := by
    rw [inclusion_scalarAssociator, ιTensorObj₃'_associator_hom]
  unfold twistedRightSnakeTerm
  rw [← assoc (ιTensorObj₃' X (PointedVec.gradedDual X) X a (-a) k k (by simp)), hh]
  simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, assoc]
  rw [baseRightSnakeTerm_shape]

lemma twistedRightSnakeTerm_self (r : A → A → A → ℂˣ) (X : PointedVec A) (a : A) :
    twistedRightSnakeTerm r X a a = (λ_ (X a)).hom := by
  rw [twistedRightSnakeTerm_eq, PointedVec.rightSnakeTerm_self]
  have hc : cupWeight r a * (r a (-a) a : ℂ) = 1 := by simp [cupWeight]
  rw [hc, one_smul]

lemma twistedRightSnakeTerm_ne (r : A → A → A → ℂˣ) (X : PointedVec A)
    (a k : A) (ha : a ≠ k) : twistedRightSnakeTerm r X a k = 0 := by
  rw [twistedRightSnakeTerm_eq, PointedVec.rightSnakeTerm_ne X a k ha, smul_zero]

lemma baseLeftSnakeTerm_shape (X : PointedVec A) (a k : A) :
    PointedVec.leftSnakeTerm X a k =
      (PointedVec.gradedDual X k) ◁
        (η_ (X a) (X a)ᘁ ≫ (X a) ◁ (PointedVec.dualFiberIso X a).inv) ≫
      ιTensorObj₃ (PointedVec.gradedDual X) X (PointedVec.gradedDual X) k a (-a) k
        (by simp [add_assoc]) ≫
      (GradedObject.Monoidal.associator (PointedVec.gradedDual X) X (PointedVec.gradedDual X)).inv k ≫
      GradedObject.Monoidal.whiskerRight (PointedVec.gradedEvaluation X) (PointedVec.gradedDual X) k ≫
      (GradedObject.Monoidal.leftUnitor (PointedVec.gradedDual X)).hom k := by
  unfold PointedVec.leftSnakeTerm
  rw [← assoc (η_ (X a) (X a)ᘁ) ((X a) ◁ (PointedVec.dualFiberIso X a).inv)
      (ιTensorObj X (PointedVec.gradedDual X) a (-a) 0 (add_neg_cancel a)),
    MonoidalCategory.whiskerLeft_comp]
  simp only [assoc]
  rw [← ιTensorObj₃_eq_assoc (PointedVec.gradedDual X) X (PointedVec.gradedDual X)
    k a (-a) k (by simp [add_assoc]) 0 (add_neg_cancel a)]

def twistedLeftSnakeTerm (r : A → A → A → ℂˣ) (X : PointedVec A) (a k : A) :
    PointedVec.gradedDual X k ⊗ 𝟙_ (FGModuleCat ℂ) ⟶ PointedVec.gradedDual X k :=
  cupWeight r a •
    ((PointedVec.gradedDual X k) ◁
      (η_ (X a) (X a)ᘁ ≫ (X a) ◁ (PointedVec.dualFiberIso X a).inv) ≫
      ιTensorObj₃ (PointedVec.gradedDual X) X (PointedVec.gradedDual X) k a (-a) k
        (by simp [add_assoc]) ≫
      (scalarAssociator r (PointedVec.gradedDual X) X (PointedVec.gradedDual X)).inv k ≫
      GradedObject.Monoidal.whiskerRight (PointedVec.gradedEvaluation X) (PointedVec.gradedDual X) k ≫
      (GradedObject.Monoidal.leftUnitor (PointedVec.gradedDual X)).hom k)

lemma twistedLeftSnakeTerm_eq (r : A → A → A → ℂˣ) (X : PointedVec A) (a k : A) :
    twistedLeftSnakeTerm r X a k =
      (cupWeight r a * (((r k a (-a))⁻¹ : ℂˣ) : ℂ)) • PointedVec.leftSnakeTerm X a k := by
  have hh : ιTensorObj₃ (PointedVec.gradedDual X) X (PointedVec.gradedDual X) k a (-a) k
      (by simp [add_assoc]) ≫
      (scalarAssociator r (PointedVec.gradedDual X) X (PointedVec.gradedDual X)).inv k =
    (((r k a (-a))⁻¹ : ℂˣ) : ℂ) •
      (ιTensorObj₃ (PointedVec.gradedDual X) X (PointedVec.gradedDual X) k a (-a) k
        (by simp [add_assoc]) ≫
      (GradedObject.Monoidal.associator (PointedVec.gradedDual X) X (PointedVec.gradedDual X)).inv k) := by
    rw [inclusion_scalarAssociator_inv, ιTensorObj₃_associator_inv]
  unfold twistedLeftSnakeTerm
  rw [← assoc (ιTensorObj₃ (PointedVec.gradedDual X) X (PointedVec.gradedDual X)
    k a (-a) k (by simp [add_assoc])), hh]
  simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, assoc]
  rw [baseLeftSnakeTerm_shape]

lemma twistedLeftSnakeTerm_self (r : A → A → A → ℂˣ)
    (hinv : ∀ a, r (-a) a (-a) * r a (-a) a = 1) (X : PointedVec A) (a : A) :
    twistedLeftSnakeTerm r X a (-a) = (ρ_ (PointedVec.gradedDual X (-a))).hom := by
  rw [twistedLeftSnakeTerm_eq, PointedVec.leftSnakeTerm_self]
  have hc : cupWeight r a * (((r (-a) a (-a))⁻¹ : ℂˣ) : ℂ) = 1 := by
    dsimp only [cupWeight]
    rw [← Units.val_mul, ← mul_inv_rev, hinv, inv_one, Units.val_one]
  rw [hc, one_smul]

lemma twistedLeftSnakeTerm_matching (r : A → A → A → ℂˣ)
    (hinv : ∀ a, r (-a) a (-a) * r a (-a) a = 1) (X : PointedVec A) (a k : A)
    (hk : k = -a) : twistedLeftSnakeTerm r X a k = (ρ_ (PointedVec.gradedDual X k)).hom := by
  subst k
  exact twistedLeftSnakeTerm_self r hinv X a

lemma twistedLeftSnakeTerm_ne (r : A → A → A → ℂˣ) (X : PointedVec A)
    (a k : A) (ha : a ≠ -k) : twistedLeftSnakeTerm r X a k = 0 := by
  rw [twistedLeftSnakeTerm_eq, PointedVec.leftSnakeTerm_ne X a k ha, smul_zero]

end Paper18.Category.QuasiFusion
