import Paper18.Category.CrossedExtensionTensorator
import Paper18.Category.CrossedExtensionRegradeUnit

/-! # Actual associativity of the regrading tensorator -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace Paper18.Category.CrossedExtension
variable {A : Type} [Fintype A] [AddGroup A]
open GradedObject.Monoidal QuasiFusion
local instance coherenceBaseMonoidal : MonoidalCategory (GradedObject A (FGModuleCat ℂ)) :=
  GradedObject.monoidalCategory

set_option maxHeartbeats 1000000 in
/-- Scalar cochain compatibility yields the actual tensor-functor
associativity square on all finite graded vector spaces. -/
theorem weightedRegrade_associativity (e : A ≃+ A) (t : A → A → ℂˣ)
    (r : A → A → A → ℂˣ)
    (ht : ∀ a b c, t a b * t (a + b) c * r (e a) (e b) (e c) =
      r a b c * t b c * t a (b + c)) (X Y Z : PointedVec A) :
    (weightedRegradeTensorIso e t X Y).hom ▷ (regradeFunctor e).obj Z ≫
        (weightedRegradeTensorIso e t (X ⊗ Y) Z).hom ≫
        (regradeFunctor e).map (scalarAssociator r X Y Z).hom =
      (scalarAssociator r ((regradeFunctor e).obj X) ((regradeFunctor e).obj Y)
        ((regradeFunctor e).obj Z)).hom ≫
        (regradeFunctor e).obj X ◁ (weightedRegradeTensorIso e t Y Z).hom ≫
        (weightedRegradeTensorIso e t X (Y ⊗ Z)).hom := by
  apply GradedObject.hom_ext
  intro k
  apply tensorObj₃'_ext (X₁ := (regradeFunctor e).obj X)
    (X₂ := (regradeFunctor e).obj Y) (X₃ := (regradeFunctor e).obj Z)
  intro a b c h
  change ιTensorObj₃' ((regradeFunctor e).obj X) ((regradeFunctor e).obj Y)
      ((regradeFunctor e).obj Z) a b c k h ≫
      (GradedObject.Monoidal.whiskerRight (weightedRegradeTensorIso e t X Y).hom
        ((regradeFunctor e).obj Z) k ≫
       (weightedRegradeTensorIso e t (X ⊗ Y) Z).hom k ≫
       (scalarAssociator r X Y Z).hom (e k)) =
    ιTensorObj₃' ((regradeFunctor e).obj X) ((regradeFunctor e).obj Y)
      ((regradeFunctor e).obj Z) a b c k h ≫
      ((scalarAssociator r ((regradeFunctor e).obj X) ((regradeFunctor e).obj Y)
        ((regradeFunctor e).obj Z)).hom k ≫
       GradedObject.Monoidal.whiskerLeft ((regradeFunctor e).obj X)
        (weightedRegradeTensorIso e t Y Z).hom k ≫
       (weightedRegradeTensorIso e t X (Y ⊗ Z)).hom k)
  dsimp only [PointedVec.instMonoidalCategory, GradedObject.monoidalCategory]
  have he : e a + e b + e c = e k := by rw [← e.map_add, ← e.map_add, h]
  conv_lhs =>
    rw [ιTensorObj₃'_eq ((regradeFunctor e).obj X) ((regradeFunctor e).obj Y)
      ((regradeFunctor e).obj Z) a b c k h (a + b) rfl, assoc, ι_tensorHom_assoc]
    dsimp only [PointedVec.id_apply, GradedObject.categoryOfGradedObjects_id]
    rw [MonoidalCategory.tensorHom_id, ← MonoidalCategory.comp_whiskerRight_assoc,
      inclusion_weightedRegradeTensorIso]
    simp only [MonoidalLinear.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul, assoc]
    rw [inclusion_weightedRegradeTensorIso_assoc]
    simp only [Linear.smul_comp, Linear.comp_smul, assoc]
    dsimp only [regradeFunctor, GradedObject.comap, Pi.comap]
    rw [← ιTensorObj₃'_eq_assoc X Y Z (e a) (e b) (e c) (e k) he
      (e (a + b)) (e.map_add a b).symm, inclusion_scalarAssociator]
  conv_rhs =>
    rw [inclusion_scalarAssociator_assoc]
    simp only [Linear.smul_comp, Linear.comp_smul, assoc]
    rw [ιTensorObj₃_eq ((regradeFunctor e).obj X) ((regradeFunctor e).obj Y)
      ((regradeFunctor e).obj Z) a b c k h (b + c) rfl, assoc, ι_tensorHom_assoc]
    dsimp only [PointedVec.id_apply, GradedObject.categoryOfGradedObjects_id]
    rw [MonoidalCategory.id_tensorHom, ← MonoidalCategory.whiskerLeft_comp_assoc,
      inclusion_weightedRegradeTensorIso]
    simp only [MonoidalLinear.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul, assoc]
    rw [inclusion_weightedRegradeTensorIso]
    simp only [Linear.smul_comp, Linear.comp_smul, assoc]
    dsimp only [regradeFunctor, GradedObject.comap, Pi.comap]
    rw [← ιTensorObj₃_eq X Y Z (e a) (e b) (e c) (e k) he
      (e (b + c)) (e.map_add b c).symm]
  simp only [smul_smul]
  congr 1
  simpa only [Units.val_mul, mul_assoc] using congrArg (fun z : ℂˣ => (z : ℂ)) (ht a b c)

end Paper18.Category.CrossedExtension
