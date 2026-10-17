import Paper18.Category.CrossedExtensionTensorator
import Paper18.Category.CrossedExtensionRegradeUnit

/-! # Actual unitality of normalized regrading tensorators -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace Paper18.Category.CrossedExtension
variable {A : Type} [Fintype A] [AddGroup A]
open GradedObject.Monoidal
local instance unitCoherenceBaseMonoidal : MonoidalCategory (GradedObject A (FGModuleCat ℂ)) :=
  GradedObject.monoidalCategory

lemma inclusion_leftUnitor_of_zero (X : PointedVec A) (a b : A) (ha : a = 0) :
    ιTensorObj (𝟙_ (PointedVec A)) X a b b (by rw [ha, zero_add]) ≫
        (GradedObject.Monoidal.leftUnitor X).hom b =
      eqToHom (congrArg (𝟙_ (PointedVec A)) ha) ▷ X b ≫
        PointedVec.unitFiberIso.hom ▷ X b ≫ (λ_ (X b)).hom := by
  subst a
  simpa only [eqToHom_refl, id_whiskerRight, id_comp] using PointedVec.inclusion_leftUnitor X b

lemma inclusion_rightUnitor_of_zero (X : PointedVec A) (a b : A) (hb : b = 0) :
    ιTensorObj X (𝟙_ (PointedVec A)) a b a (by rw [hb, add_zero]) ≫
        (GradedObject.Monoidal.rightUnitor X).hom a =
      X a ◁ eqToHom (congrArg (𝟙_ (PointedVec A)) hb) ≫
        X a ◁ PointedVec.unitFiberIso.hom ≫ (ρ_ (X a)).hom := by
  subst b
  simpa only [eqToHom_refl, whiskerLeft_id, id_comp] using PointedVec.inclusion_rightUnitor X a

instance unitLeftInclusion_isIso (X : PointedVec A) (k : A) :
    IsIso (ιTensorObj (𝟙_ (PointedVec A)) X 0 k k (zero_add k)) := by
  letI := GradedObject.isIso_apply_of_isIso (GradedObject.Monoidal.leftUnitor X).hom k
  haveI : IsIso (ιTensorObj (𝟙_ (PointedVec A)) X 0 k k (zero_add k) ≫
      (GradedObject.Monoidal.leftUnitor X).hom k) := by
    rw [PointedVec.inclusion_leftUnitor]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((GradedObject.Monoidal.leftUnitor X).hom k)

instance unitRightInclusion_isIso (X : PointedVec A) (k : A) :
    IsIso (ιTensorObj X (𝟙_ (PointedVec A)) k 0 k (add_zero k)) := by
  letI := GradedObject.isIso_apply_of_isIso (GradedObject.Monoidal.rightUnitor X).hom k
  haveI : IsIso (ιTensorObj X (𝟙_ (PointedVec A)) k 0 k (add_zero k) ≫
      (GradedObject.Monoidal.rightUnitor X).hom k) := by
    rw [PointedVec.inclusion_rightUnitor]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((GradedObject.Monoidal.rightUnitor X).hom k)

/-- Normalization in the first degree proves the actual left unit diagram. -/
theorem weightedRegrade_left_unitality (e : A ≃+ A) (t : A → A → ℂˣ)
    (ht : ∀ a, t 0 a = 1) (X : PointedVec A) :
    (λ_ ((regradeFunctor e).obj X)).hom =
      (regradeUnitIso e).hom ▷ (regradeFunctor e).obj X ≫
        (weightedRegradeTensorIso e t (𝟙_ (PointedVec A)) X).hom ≫
        (regradeFunctor e).map (λ_ X).hom := by
  apply GradedObject.hom_ext
  intro k
  apply (cancel_epi (ιTensorObj (𝟙_ (PointedVec A)) ((regradeFunctor e).obj X)
    0 k k (zero_add k))).mp
  change ιTensorObj (𝟙_ (PointedVec A)) ((regradeFunctor e).obj X) 0 k k (zero_add k) ≫
      (GradedObject.Monoidal.leftUnitor ((regradeFunctor e).obj X)).hom k =
    ιTensorObj (𝟙_ (PointedVec A)) ((regradeFunctor e).obj X) 0 k k (zero_add k) ≫
      GradedObject.Monoidal.whiskerRight (regradeUnitIso e).hom ((regradeFunctor e).obj X) k ≫
      (weightedRegradeTensorIso e t (𝟙_ (PointedVec A)) X).hom k ≫
      (GradedObject.Monoidal.leftUnitor X).hom (e k)
  rw [PointedVec.inclusion_leftUnitor, ι_tensorHom_assoc]
  dsimp only [PointedVec.id_apply, GradedObject.categoryOfGradedObjects_id]
  rw [MonoidalCategory.tensorHom_id, inclusion_weightedRegradeTensorIso_assoc, ht]
  simp only [Units.val_one, one_smul, regradeUnitIso_hom_zero]
  dsimp only [regradeFunctor, GradedObject.comap, Pi.comap]
  rw [inclusion_leftUnitor_of_zero X (e 0) (e k) e.map_zero]
  rw [← MonoidalCategory.comp_whiskerRight_assoc]
  simp only [eqToHom_trans, eqToHom_refl, id_whiskerRight, id_comp]

/-- Normalization in the second degree proves the actual right unit diagram. -/
theorem weightedRegrade_right_unitality (e : A ≃+ A) (t : A → A → ℂˣ)
    (ht : ∀ a, t a 0 = 1) (X : PointedVec A) :
    (ρ_ ((regradeFunctor e).obj X)).hom =
      (regradeFunctor e).obj X ◁ (regradeUnitIso e).hom ≫
        (weightedRegradeTensorIso e t X (𝟙_ (PointedVec A))).hom ≫
        (regradeFunctor e).map (ρ_ X).hom := by
  apply GradedObject.hom_ext
  intro k
  apply (cancel_epi (ιTensorObj ((regradeFunctor e).obj X) (𝟙_ (PointedVec A))
    k 0 k (add_zero k))).mp
  change ιTensorObj ((regradeFunctor e).obj X) (𝟙_ (PointedVec A)) k 0 k (add_zero k) ≫
      (GradedObject.Monoidal.rightUnitor ((regradeFunctor e).obj X)).hom k =
    ιTensorObj ((regradeFunctor e).obj X) (𝟙_ (PointedVec A)) k 0 k (add_zero k) ≫
      GradedObject.Monoidal.whiskerLeft ((regradeFunctor e).obj X) (regradeUnitIso e).hom k ≫
      (weightedRegradeTensorIso e t X (𝟙_ (PointedVec A))).hom k ≫
      (GradedObject.Monoidal.rightUnitor X).hom (e k)
  rw [PointedVec.inclusion_rightUnitor, ι_tensorHom_assoc]
  dsimp only [PointedVec.id_apply, GradedObject.categoryOfGradedObjects_id]
  rw [MonoidalCategory.id_tensorHom, inclusion_weightedRegradeTensorIso_assoc, ht]
  simp only [Units.val_one, one_smul, regradeUnitIso_hom_zero]
  dsimp only [regradeFunctor, GradedObject.comap, Pi.comap]
  rw [inclusion_rightUnitor_of_zero X (e k) (e 0) e.map_zero]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [eqToHom_trans, eqToHom_refl, whiskerLeft_id, id_comp]


end Paper18.Category.CrossedExtension
