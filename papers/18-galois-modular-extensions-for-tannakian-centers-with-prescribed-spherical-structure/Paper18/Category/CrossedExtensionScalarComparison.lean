import Paper18.Category.CrossedExtensionTensorator
import Paper18.Category.CrossedExtensionActionBasic

/-! # Actual tensor compatibility of scalar regrading comparisons -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace Paper18.Category.CrossedExtension
variable {A : Type} [Fintype A] [AddGroup A]
open GradedObject.Monoidal
local instance scalarComparisonBaseMonoidal : MonoidalCategory (GradedObject A (FGModuleCat ℂ)) :=
  GradedObject.monoidalCategory

theorem weightedRegrade_identity_tensor (X Y : PointedVec A) :
    (weightedRegradeTensorIso (AddEquiv.refl A) (fun _ _ => 1) X Y).hom = 𝟙 (X ⊗ Y) := by
  apply GradedObject.hom_ext
  intro k
  apply tensorObj_ext
  intro a b h
  change ιTensorObj X Y a b k h ≫
      (weightedRegradeTensorIso (AddEquiv.refl A) (fun _ _ => 1) X Y).hom k = _
  have hh := inclusion_weightedRegradeTensorIso (AddEquiv.refl A) (fun _ _ => 1) X Y a b k h
  simpa only [Units.val_one, one_smul] using hh

/-- Composition of actual weighted regradings has the actual product
tensorator on each homogeneous summand. -/
theorem weightedRegrade_comp_tensor (e f : A ≃+ A) (t u : A → A → ℂˣ)
    (X Y : PointedVec A) :
    (weightedRegradeTensorIso e t ((regradeFunctor f).obj X) ((regradeFunctor f).obj Y)).hom ≫
        (regradeFunctor e).map (weightedRegradeTensorIso f u X Y).hom =
      (weightedRegradeTensorIso (e.trans f)
        (fun a b => t a b * u (e a) (e b)) X Y).hom := by
  apply GradedObject.hom_ext
  intro k
  apply tensorObj_ext
  intro a b h
  change ιTensorObj ((regradeFunctor e).obj ((regradeFunctor f).obj X))
      ((regradeFunctor e).obj ((regradeFunctor f).obj Y)) a b k h ≫
      ((weightedRegradeTensorIso e t ((regradeFunctor f).obj X) ((regradeFunctor f).obj Y)).hom k ≫
        (weightedRegradeTensorIso f u X Y).hom (e k)) = _
  rw [inclusion_weightedRegradeTensorIso_assoc]
  rw [Linear.smul_comp, inclusion_weightedRegradeTensorIso]
  have hh := inclusion_weightedRegradeTensorIso (e.trans f)
    (fun a b => t a b * u (e a) (e b)) X Y a b k h
  simpa only [regradeFunctor, GradedObject.comap, Pi.comap,
    AddEquiv.trans_apply, Units.val_mul, smul_smul] using hh.symm

/-- The scalar tensorator equation gives an actual monoidal comparison
square for every actual pair of graded vector spaces. -/
theorem weightedRegrade_comparison_tensor (e f : A ≃+ A)
    (h : ∀ a, e a = f a) (t u : A → A → ℂˣ) (s : A → ℂˣ)
    (hs : ∀ a b, t a b * s (a + b) = s a * s b * u a b)
    (X Y : PointedVec A) :
    (weightedRegradeTensorIso e t X Y).hom ≫
        (pullbackScalarNatIso e f h s).hom.app (X ⊗ Y) =
      ((pullbackScalarNatIso e f h s).hom.app X ⊗ₘ
        (pullbackScalarNatIso e f h s).hom.app Y) ≫
        (weightedRegradeTensorIso f u X Y).hom := by
  have hef : e = f := AddEquiv.ext h
  subst f
  apply GradedObject.hom_ext
  intro k
  apply tensorObj_ext
  intro a b hab
  change ιTensorObj ((regradeFunctor e).obj X) ((regradeFunctor e).obj Y) a b k hab ≫
      ((weightedRegradeTensorIso e t X Y).hom k ≫
        (pullbackScalarNatIso e e h s).hom.app (X ⊗ Y) k) =
    ιTensorObj ((regradeFunctor e).obj X) ((regradeFunctor e).obj Y) a b k hab ≫
      (GradedObject.Monoidal.tensorHom ((pullbackScalarNatIso e e h s).hom.app X)
        ((pullbackScalarNatIso e e h s).hom.app Y) k ≫
        (weightedRegradeTensorIso e u X Y).hom k)
  rw [inclusion_weightedRegradeTensorIso_assoc, ι_tensorHom_assoc]
  simp only [pullbackScalarNatIso_hom_app, eqToHom_refl]
  rw [MonoidalCategory.tensorHom_def]
  simp only [MonoidalLinear.smul_whiskerRight, MonoidalLinear.whiskerLeft_smul,
    Linear.smul_comp, Linear.comp_smul, smul_smul]
  dsimp only [PointedVec.instMonoidalCategory, GradedObject.monoidalCategory,
    regradeFunctor, GradedObject.comap, Pi.comap]
  simp only [id_whiskerRight, whiskerLeft_id, id_comp]
  change ((s k : ℂ) * (t a b : ℂ)) • ιTensorObj X Y (e a) (e b) (e k)
      (by rw [← e.map_add, hab]) =
    ((s b : ℂ) * (s a : ℂ)) •
      (ιTensorObj ((regradeFunctor e).obj X) ((regradeFunctor e).obj Y) a b k hab ≫
        (weightedRegradeTensorIso e u X Y).hom k)
  rw [inclusion_weightedRegradeTensorIso]
  simp only [smul_smul]
  congr 1
  have hc := congrArg (fun z : ℂˣ => (z : ℂ)) (hs a b)
  simpa only [Units.val_mul, hab, mul_comm, mul_left_comm, mul_assoc] using hc

end Paper18.Category.CrossedExtension
