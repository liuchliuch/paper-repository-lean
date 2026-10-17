import Paper18.Category.PointedBiproducts
import Paper18.Category.PointedLinear

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Category
open scoped BigOperators
open Classical

namespace Paper18.Category.PointedVec

variable {A : Type} [Fintype A] [AddGroup A]

local instance rigidGradedMonoidal : MonoidalCategory (GradedObject A (FGModuleCat ℂ)) :=
  GradedObject.monoidalCategory

/-- Vector-space duality with the group degree inverted. -/
def gradedDual (X : PointedVec A) : PointedVec A := fun a => (X (-a))ᘁ

def dualFiberIso (X : PointedVec A) (a : A) : gradedDual X (-a) ≅ (X a)ᘁ :=
  eqToIso (congrArg (fun b => (X b)ᘁ) (neg_neg a))

def unitFiberIso : ((𝟙_ (PointedVec A)) (0 : A)) ≅ 𝟙_ (FGModuleCat ℂ) :=
  GradedObject.Monoidal.tensorUnit₀

def mapFromUnit {Z : PointedVec A} (f : 𝟙_ (FGModuleCat ℂ) ⟶ Z 0) :
    𝟙_ (PointedVec A) ⟶ Z := fun a =>
  if ha : a = 0 then
    eqToHom (congrArg (𝟙_ (PointedVec A)) ha) ≫ unitFiberIso.hom ≫ f ≫
      eqToHom (congrArg Z ha).symm
  else 0

def mapToUnit {Z : PointedVec A} (f : Z 0 ⟶ 𝟙_ (FGModuleCat ℂ)) :
    Z ⟶ 𝟙_ (PointedVec A) := fun a =>
  if ha : a = 0 then
    eqToHom (congrArg Z ha) ≫ f ≫ unitFiberIso.inv ≫
      eqToHom (congrArg (𝟙_ (PointedVec A)) ha).symm
  else 0

@[simp] lemma mapFromUnit_zero {Z : PointedVec A} (f : 𝟙_ (FGModuleCat ℂ) ⟶ Z 0) :
    mapFromUnit f 0 = unitFiberIso.hom ≫ f := by simp [mapFromUnit]

@[simp] lemma mapToUnit_zero {Z : PointedVec A} (f : Z 0 ⟶ 𝟙_ (FGModuleCat ℂ)) :
    mapToUnit f 0 = f ≫ unitFiberIso.inv := by simp [mapToUnit]

@[simp] lemma mapToUnit_ne {Z : PointedVec A} (f : Z 0 ⟶ 𝟙_ (FGModuleCat ℂ))
    (a : A) (ha : a ≠ 0) : mapToUnit f a = 0 := by simp [mapToUnit, ha]

open GradedObject.Monoidal

def gradedCoevaluationZero (X : PointedVec A) :
    𝟙_ (FGModuleCat ℂ) ⟶ GradedObject.Monoidal.tensorObj X (gradedDual X) 0 :=
  ∑ a, η_ (X a) (X a)ᘁ ≫ (X a) ◁ (dualFiberIso X a).inv ≫
    ιTensorObj X (gradedDual X) a (-a) 0 (add_neg_cancel a)

def gradedCoevaluation (X : PointedVec A) :
    𝟙_ (PointedVec A) ⟶ GradedObject.Monoidal.tensorObj X (gradedDual X) :=
  mapFromUnit (gradedCoevaluationZero X)

def dualPairIso (X : PointedVec A) (a b : A) (h : a + b = 0) :
    gradedDual X a ≅ (X b)ᘁ :=
  eqToIso (congrArg (gradedDual X) (eq_neg_of_add_eq_zero_left h)) ≪≫ dualFiberIso X b

def gradedEvaluationZero (X : PointedVec A) :
    GradedObject.Monoidal.tensorObj (gradedDual X) X 0 ⟶ 𝟙_ (FGModuleCat ℂ) :=
  tensorObjDesc (fun a b h => (dualPairIso X a b h).hom ▷ (X b) ≫ ε_ (X b) (X b)ᘁ)

def gradedEvaluation (X : PointedVec A) :
    GradedObject.Monoidal.tensorObj (gradedDual X) X ⟶ 𝟙_ (PointedVec A) :=
  mapToUnit (gradedEvaluationZero X)

omit [Fintype A] in
@[simp] lemma dualPairIso_canonical (X : PointedVec A) (a : A) :
    dualPairIso X (-a) a (neg_add_cancel a) = dualFiberIso X a := by
  simp [dualPairIso]

@[reassoc]
lemma inclusion_evaluation_zero (X : PointedVec A) (a b : A) (h : a + b = 0) :
    ιTensorObj (gradedDual X) X a b 0 h ≫ gradedEvaluation X 0 =
      (dualPairIso X a b h).hom ▷ (X b) ≫ ε_ (X b) (X b)ᘁ ≫ unitFiberIso.inv := by
  simp [gradedEvaluation, gradedEvaluationZero, mapToUnit]

@[reassoc]
lemma inclusion_rightUnitor (X : PointedVec A) (a : A) :
    ιTensorObj X (𝟙_ (PointedVec A)) a 0 a (add_zero a) ≫
        (GradedObject.Monoidal.rightUnitor X).hom a =
      (X a) ◁ unitFiberIso.hom ≫ (ρ_ (X a)).hom := by
  exact GradedObject.ι_mapBifunctorRightUnitor_hom_apply
    (curriedTensor (FGModuleCat ℂ)) (𝟙_ (FGModuleCat ℂ))
    (rightUnitorNatIso (FGModuleCat ℂ)) (fun p : A × A => p.1 + p.2) add_zero X a

@[reassoc]
lemma inclusion_leftUnitor (X : PointedVec A) (a : A) :
    ιTensorObj (𝟙_ (PointedVec A)) X 0 a a (zero_add a) ≫
        (GradedObject.Monoidal.leftUnitor X).hom a =
      unitFiberIso.hom ▷ (X a) ≫ (λ_ (X a)).hom := by
  exact GradedObject.ι_mapBifunctorLeftUnitor_hom_apply
    (curriedTensor (FGModuleCat ℂ)) (𝟙_ (FGModuleCat ℂ))
    (leftUnitorNatIso (FGModuleCat ℂ)) (fun p : A × A => p.1 + p.2) zero_add X a

def rightSnakeTerm (X : PointedVec A) (a k : A) :
    𝟙_ (FGModuleCat ℂ) ⊗ X k ⟶ X k :=
  (η_ (X a) (X a)ᘁ ≫ (X a) ◁ (dualFiberIso X a).inv ≫
      ιTensorObj X (gradedDual X) a (-a) 0 (add_neg_cancel a)) ▷ X k ≫
    ιTensorObj (GradedObject.Monoidal.tensorObj X (gradedDual X)) X 0 k k (zero_add k) ≫
    (GradedObject.Monoidal.associator X (gradedDual X) X).hom k ≫
    GradedObject.Monoidal.whiskerLeft X (gradedEvaluation X) k ≫
    (GradedObject.Monoidal.rightUnitor X).hom k

set_option maxHeartbeats 1000000 in
lemma rightSnakeTerm_formula_at (X : PointedVec A) (a k l : A) (hl : -a + k = l) :
    rightSnakeTerm X a k =
      (η_ (X a) (X a)ᘁ ≫ (X a) ◁ (dualFiberIso X a).inv) ▷ X k ≫
        (α_ (X a) (gradedDual X (-a)) (X k)).hom ≫
        (X a) ◁ (ιTensorObj (gradedDual X) X (-a) k l hl ≫
          gradedEvaluation X l) ≫
        ιTensorObj X (𝟙_ (PointedVec A)) a l k (by rw [← hl]; simp [← add_assoc]) ≫
        (GradedObject.Monoidal.rightUnitor X).hom k := by
  unfold rightSnakeTerm
  rw [← Category.assoc (η_ (X a) (X a)ᘁ) ((X a) ◁ (dualFiberIso X a).inv)
      (ιTensorObj X (gradedDual X) a (-a) 0 (add_neg_cancel a)),
    MonoidalCategory.comp_whiskerRight, assoc,
    ← ιTensorObj₃'_eq_assoc X (gradedDual X) X a (-a) k k (by simp) 0 (add_neg_cancel a),
    ιTensorObj₃'_associator_hom_assoc,
    ιTensorObj₃_eq X (gradedDual X) X a (-a) k k (by simp) l hl,
    assoc, ι_tensorHom_assoc,
    GradedObject.categoryOfGradedObjects_id,
    ← MonoidalCategory.id_tensorHom, ← MonoidalCategory.id_tensorHom,
    ← MonoidalCategory.id_tensor_comp_assoc,
    MonoidalCategory.id_tensorHom]
  rw [MonoidalCategory.id_tensorHom]

set_option maxHeartbeats 1000000 in
lemma rightSnakeTerm_self (X : PointedVec A) (a : A) :
    rightSnakeTerm X a a = (λ_ (X a)).hom := by
  rw [rightSnakeTerm_formula_at X a a 0 (neg_add_cancel a)]
  rw [inclusion_evaluation_zero, dualPairIso_canonical]
  rw [inclusion_rightUnitor]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc (X a) unitFiberIso.inv unitFiberIso.hom, Iso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  letI : ExactPairing (X a) (gradedDual X (-a)) := exactPairingCongrRight (dualFiberIso X a)
  have hs := ExactPairing.evaluation_coevaluation (X a) (gradedDual X (-a))
  have hs' := congrArg (fun f => f ≫ (ρ_ (X a)).hom) hs
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hs'
  change (η_ (X a) (X a)ᘁ ≫ (X a) ◁ (dualFiberIso X a).inv) ▷ X a ≫
    (α_ (X a) (gradedDual X (-a)) (X a)).hom ≫
    (X a) ◁ ((dualFiberIso X a).hom ▷ X a ≫ ε_ (X a) (X a)ᘁ) ≫
    (ρ_ (X a)).hom = (λ_ (X a)).hom at hs'
  simpa only [MonoidalCategory.whiskerLeft_comp, Category.assoc] using hs'

lemma rightSnakeTerm_ne (X : PointedVec A) (a k : A) (ha : a ≠ k) :
    rightSnakeTerm X a k = 0 := by
  rw [rightSnakeTerm_formula_at X a k (-a + k) rfl]
  have hdeg : -a + k ≠ 0 := by
    intro h
    apply ha
    have hh := congrArg (fun z => a + z) h
    simpa only [← add_assoc, add_neg_cancel, zero_add, add_zero] using hh.symm
  simp [gradedEvaluation, mapToUnit, hdeg]

def rightSnake (X : PointedVec A) : X ⟶ X :=
  (λ_ X).inv ≫ gradedCoevaluation X ▷ X ≫
    (α_ X (gradedDual X) X).hom ≫ X ◁ gradedEvaluation X ≫ (ρ_ X).hom

set_option maxHeartbeats 1000000 in
lemma rightSnake_expansion (X : PointedVec A) (k : A) :
    rightSnake X k = (λ_ (X k)).inv ≫ ∑ a, rightSnakeTerm X a k := by
  change (GradedObject.Monoidal.leftUnitor X).inv k ≫
      GradedObject.Monoidal.whiskerRight (gradedCoevaluation X) X k ≫
      (GradedObject.Monoidal.associator X (gradedDual X) X).hom k ≫
      GradedObject.Monoidal.whiskerLeft X (gradedEvaluation X) k ≫
      (GradedObject.Monoidal.rightUnitor X).hom k = _
  rw [leftUnitor_inv_apply]
  simp only [Category.assoc]
  rw [ι_tensorHom_assoc,
    GradedObject.categoryOfGradedObjects_id, MonoidalCategory.tensorHom_id]
  simp only [gradedCoevaluation, mapFromUnit_zero, unitFiberIso]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, Iso.inv_hom_id_assoc]
  simp only [gradedCoevaluationZero, sum_whiskerRight, Preadditive.sum_comp,
    rightSnakeTerm]

lemma rightSnake_eq_id (X : PointedVec A) : rightSnake X = 𝟙 X := by
  funext k
  rw [rightSnake_expansion]
  have hsum : (∑ a, rightSnakeTerm X a k) = (λ_ (X k)).hom := by
    rw [Finset.sum_eq_single k]
    · exact rightSnakeTerm_self X k
    · intro a _ ha
      exact rightSnakeTerm_ne X a k ha
    · simp
  rw [hsum, Iso.inv_hom_id]
  rfl

lemma graded_evaluation_coevaluation (X : PointedVec A) :
    gradedCoevaluation X ▷ X ≫ (α_ X (gradedDual X) X).hom ≫ X ◁ gradedEvaluation X =
      (λ_ X).hom ≫ (ρ_ X).inv := by
  apply (cancel_epi (λ_ X).inv).mp
  apply (cancel_mono (ρ_ X).hom).mp
  simpa only [rightSnake, Category.assoc, Iso.inv_hom_id, Iso.hom_inv_id,
    Category.id_comp, Category.comp_id] using rightSnake_eq_id X

def leftSnakeTerm (X : PointedVec A) (a k : A) :
    gradedDual X k ⊗ 𝟙_ (FGModuleCat ℂ) ⟶ gradedDual X k :=
  (gradedDual X k) ◁ (η_ (X a) (X a)ᘁ ≫ (X a) ◁ (dualFiberIso X a).inv ≫
      ιTensorObj X (gradedDual X) a (-a) 0 (add_neg_cancel a)) ≫
    ιTensorObj (gradedDual X) (GradedObject.Monoidal.tensorObj X (gradedDual X)) k 0 k (add_zero k) ≫
    (GradedObject.Monoidal.associator (gradedDual X) X (gradedDual X)).inv k ≫
    GradedObject.Monoidal.whiskerRight (gradedEvaluation X) (gradedDual X) k ≫
    (GradedObject.Monoidal.leftUnitor (gradedDual X)).hom k

set_option maxHeartbeats 1000000 in
lemma leftSnakeTerm_formula_at (X : PointedVec A) (a k l : A) (hl : k + a = l) :
    leftSnakeTerm X a k =
      (gradedDual X k) ◁ (η_ (X a) (X a)ᘁ ≫ (X a) ◁ (dualFiberIso X a).inv) ≫
        (α_ (gradedDual X k) (X a) (gradedDual X (-a))).inv ≫
        (ιTensorObj (gradedDual X) X k a l hl ≫ gradedEvaluation X l) ▷ gradedDual X (-a) ≫
        ιTensorObj (𝟙_ (PointedVec A)) (gradedDual X) l (-a) k
          (by rw [← hl]; simp [add_assoc]) ≫
        (GradedObject.Monoidal.leftUnitor (gradedDual X)).hom k := by
  unfold leftSnakeTerm
  rw [← Category.assoc (η_ (X a) (X a)ᘁ) ((X a) ◁ (dualFiberIso X a).inv)
      (ιTensorObj X (gradedDual X) a (-a) 0 (add_neg_cancel a)),
    MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [← ιTensorObj₃_eq_assoc (gradedDual X) X (gradedDual X) k a (-a) k
      (by simp [add_assoc]) 0 (add_neg_cancel a),
    ιTensorObj₃_associator_inv_assoc,
    ιTensorObj₃'_eq (gradedDual X) X (gradedDual X) k a (-a) k (by simp [add_assoc]) l hl,
    assoc, ι_tensorHom_assoc,
    GradedObject.categoryOfGradedObjects_id,
    ← MonoidalCategory.tensorHom_id,
    ← MonoidalCategory.comp_tensor_id_assoc,
    MonoidalCategory.tensorHom_id]

set_option maxHeartbeats 1000000 in
lemma leftSnakeTerm_self (X : PointedVec A) (a : A) :
    leftSnakeTerm X a (-a) = (ρ_ (gradedDual X (-a))).hom := by
  rw [leftSnakeTerm_formula_at X a (-a) 0 (neg_add_cancel a),
    inclusion_evaluation_zero, dualPairIso_canonical, inclusion_leftUnitor]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [← MonoidalCategory.comp_whiskerRight_assoc unitFiberIso.inv unitFiberIso.hom,
    Iso.inv_hom_id, MonoidalCategory.id_whiskerRight, Category.id_comp]
  letI : ExactPairing (X a) (gradedDual X (-a)) := exactPairingCongrRight (dualFiberIso X a)
  have hs := ExactPairing.coevaluation_evaluation (X a) (gradedDual X (-a))
  have hs' := congrArg (fun f => f ≫ (λ_ (gradedDual X (-a))).hom) hs
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hs'
  change (gradedDual X (-a)) ◁
      (η_ (X a) (X a)ᘁ ≫ (X a) ◁ (dualFiberIso X a).inv) ≫
    (α_ (gradedDual X (-a)) (X a) (gradedDual X (-a))).inv ≫
    ((dualFiberIso X a).hom ▷ X a ≫ ε_ (X a) (X a)ᘁ) ▷ gradedDual X (-a) ≫
    (λ_ (gradedDual X (-a))).hom = (ρ_ (gradedDual X (-a))).hom at hs'
  simpa only [MonoidalCategory.comp_whiskerRight, Category.assoc] using hs'

lemma leftSnakeTerm_matching (X : PointedVec A) (a k : A) (hk : k = -a) :
    leftSnakeTerm X a k = (ρ_ (gradedDual X k)).hom := by
  subst k
  exact leftSnakeTerm_self X a

lemma leftSnakeTerm_ne (X : PointedVec A) (a k : A) (ha : a ≠ -k) :
    leftSnakeTerm X a k = 0 := by
  rw [leftSnakeTerm_formula_at X a k (k + a) rfl]
  have hdeg : k + a ≠ 0 := by
    intro h
    apply ha
    exact eq_neg_of_add_eq_zero_right h
  simp [gradedEvaluation, mapToUnit, hdeg]

def leftSnake (X : PointedVec A) : gradedDual X ⟶ gradedDual X :=
  (ρ_ (gradedDual X)).inv ≫ (gradedDual X) ◁ gradedCoevaluation X ≫
    (α_ (gradedDual X) X (gradedDual X)).inv ≫
    gradedEvaluation X ▷ gradedDual X ≫ (λ_ (gradedDual X)).hom

set_option maxHeartbeats 1000000 in
lemma leftSnake_expansion (X : PointedVec A) (k : A) :
    leftSnake X k = (ρ_ (gradedDual X k)).inv ≫ ∑ a, leftSnakeTerm X a k := by
  change (GradedObject.Monoidal.rightUnitor (gradedDual X)).inv k ≫
      GradedObject.Monoidal.whiskerLeft (gradedDual X) (gradedCoevaluation X) k ≫
      (GradedObject.Monoidal.associator (gradedDual X) X (gradedDual X)).inv k ≫
      GradedObject.Monoidal.whiskerRight (gradedEvaluation X) (gradedDual X) k ≫
      (GradedObject.Monoidal.leftUnitor (gradedDual X)).hom k = _
  rw [rightUnitor_inv_apply]
  simp only [Category.assoc]
  rw [ι_tensorHom_assoc, GradedObject.categoryOfGradedObjects_id, MonoidalCategory.id_tensorHom]
  simp only [gradedCoevaluation, mapFromUnit_zero, unitFiberIso]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id_assoc]
  simp only [gradedCoevaluationZero, whiskerLeft_sum, Preadditive.sum_comp, leftSnakeTerm]

lemma leftSnake_eq_id (X : PointedVec A) : leftSnake X = 𝟙 (gradedDual X) := by
  funext k
  rw [leftSnake_expansion]
  have hsum : (∑ a, leftSnakeTerm X a k) = (ρ_ (gradedDual X k)).hom := by
    rw [Finset.sum_eq_single (-k)]
    · exact leftSnakeTerm_matching X (-k) k (neg_neg k).symm
    · intro a _ ha
      exact leftSnakeTerm_ne X a k ha
    · simp
  rw [hsum, Iso.inv_hom_id]
  rfl

lemma graded_coevaluation_evaluation (X : PointedVec A) :
    (gradedDual X) ◁ gradedCoevaluation X ≫
        (α_ (gradedDual X) X (gradedDual X)).inv ≫ gradedEvaluation X ▷ gradedDual X =
      (ρ_ (gradedDual X)).hom ≫ (λ_ (gradedDual X)).inv := by
  apply (cancel_epi (ρ_ (gradedDual X)).inv).mp
  apply (cancel_mono (λ_ (gradedDual X)).hom).mp
  simpa only [leftSnake, Category.assoc, Iso.inv_hom_id, Iso.hom_inv_id,
    Category.id_comp, Category.comp_id] using leftSnake_eq_id X

/-- The actual convolution category is rigid: both triangle identities are
proved from the finite sum of ordinary vector-space cups and caps. -/
instance gradedExactPairing (X : PointedVec A) : ExactPairing X (gradedDual X) where
  coevaluation' := gradedCoevaluation X
  evaluation' := gradedEvaluation X
  coevaluation_evaluation' := graded_coevaluation_evaluation X
  evaluation_coevaluation' := graded_evaluation_coevaluation X

instance hasRightDual (X : PointedVec A) : HasRightDual X where
  rightDual := gradedDual X

instance rightRigidCategory : RightRigidCategory (PointedVec A) where

end Paper18.Category.PointedVec
