import Paper18.Category.CrossedExtensionInnerCenterConjugationFunctor
import Paper18.Category.DrinfeldInnerTrivializationComparison

/-! # Actual tensor-coordinate helpers for kernel conjugation -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open GradedObject.Monoidal
namespace Paper18.Category.CrossedExtension
variable {A : Type} [Fintype A] [AddGroup A]

/-- The inverse weighted tensorator is computed on actual convolution
summands in the original input degrees. -/
@[reassoc] lemma inclusion_weightedRegradeTensorIso_inv (e : A ≃+ A)
    (t : A → A → ℂˣ) (X Y : PointedVec A) (a b k : A) (h : a + b = k) :
    ιTensorObj X Y (e a) (e b) (e k) (by rw [← e.map_add, h]) ≫
        (weightedRegradeTensorIso e t X Y).inv k =
      (((t a b)⁻¹ : ℂˣ) : ℂ) •
        ιTensorObj ((regradeFunctor e).obj X) ((regradeFunctor e).obj Y) a b k h := by
  let Q := weightedRegradeTensorIso e t X Y
  apply (cancel_mono ((GradedObject.eval k).mapIso Q).hom).mp
  change (_ ≫ Q.inv k) ≫ Q.hom k = (_ • _) ≫ Q.hom k
  have hi := congrFun Q.inv_hom_id k
  change Q.inv k ≫ Q.hom k = 𝟙 _ at hi
  rw [Category.assoc, hi, comp_id, Linear.smul_comp]
  rw [inclusion_weightedRegradeTensorIso]
  simp only [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

open QuasiFusion FiniteCohomologyKilling PointedVec
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance innerConjugationTensorFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

@[simp] lemma kernelLineImageIso_hom_apply (g : KillingExtension G)
    (k : KillingKernel G) (a : Additive (KillingKernel G)) :
    (kernelLineImageIso ω g k).hom a =
      eqToHom (congrArg (fun X : CocycleVec (kernelCocycle ω) => X a)
        (kernelLine_image_eq ω g k)) :=
  GradedObject.eqToHom_apply (FGModuleCat ℂ) (kernelLine_image_eq ω g k) a

@[simp] lemma kernelLineImageIso_inv_apply (g : KillingExtension G)
    (k : KillingKernel G) (a : Additive (KillingKernel G)) :
    (kernelLineImageIso ω g k).inv a =
      eqToHom (congrArg (fun X : CocycleVec (kernelCocycle ω) => X a)
        (kernelLine_image_eq ω g k).symm) :=
  GradedObject.eqToHom_apply (FGModuleCat ℂ) (kernelLine_image_eq ω g k).symm a

end Paper18.Category.CrossedExtension
