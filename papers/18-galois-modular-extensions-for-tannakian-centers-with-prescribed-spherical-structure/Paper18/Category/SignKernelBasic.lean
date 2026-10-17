import Paper18.Category.FixedBoundaryGrading
import Paper18.Category.FusionSubcategoryPivotal

/-! # The actual positive full fusion subcategory of a tensor character

Objects satisfy the actual natural-transformation equation χ_X = id_X.
Finite semisimplicity and rigidity are inherited from actual decompositions;
no decomposition or dual-closure laws are supplied as fields.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.SignKernel
open FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  (χ : 𝟭 C ≅ 𝟭 C)

/-- Homogeneity descends along actual retraction diagrams. -/
lemma homogeneous_retract {g : ZMod 2} {X Y : C} (r : Retract X Y)
    (hY : Homogeneous χ g Y) : Homogeneous χ g X := by
  have hn := χ.hom.naturality r.i
  change r.i ≫ χ.hom.app Y = χ.hom.app X ≫ r.i at hn
  have h := congrArg (fun k => k ≫ r.r) hn
  rw [hY] at h
  simpa [Homogeneous, Category.assoc, r.retract] using h.symm

def positiveProperty : ObjectProperty C := Homogeneous χ 0
abbrev Positive := (positiveProperty χ).FullSubcategory
def inclusion : Positive χ ⥤ C := (positiveProperty χ).ι

@[simp] lemma mem_positive (X : C) : positiveProperty χ X ↔ χ.hom.app X = 𝟙 X := by
  simp [positiveProperty, Homogeneous]

variable [HasFiniteBiproducts C]

instance positiveProperty_isAdditive : IsAdditiveFullProperty (positiveProperty χ) where
  of_retract r hY := homogeneous_retract χ r hY
  biproduct f hf := homogeneous_biproduct χ f 0 hf

instance inclusion_additive : (inclusion χ).Additive := by
  dsimp [inclusion]; infer_instance
instance inclusion_linear : (inclusion χ).Linear ℂ := by
  dsimp [inclusion]; infer_instance
instance inclusion_full : (inclusion χ).Full := by
  dsimp [inclusion]; infer_instance
instance inclusion_faithful : (inclusion χ).Faithful := by
  dsimp [inclusion]; infer_instance

section Monoidal
variable [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [NatTrans.IsMonoidal χ.hom]

instance positiveProperty_isMonoidal : (positiveProperty χ).IsMonoidal where
  prop_unit := homogeneous_unit χ
  prop_tensor _ _ hX hY := by
    simpa [positiveProperty, Homogeneous] using homogeneous_tensor χ hX hY

instance inclusion_monoidal : (inclusion χ).Monoidal := by
  dsimp [inclusion]; infer_instance

instance inclusion_braided [BraidedCategory C] : (inclusion χ).Braided := by
  dsimp [inclusion]; infer_instance

end Monoidal

section Semisimple
variable [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

instance finiteDimensional_hom (X Y : Positive χ) : FiniteDimensional ℂ (X ⟶ Y) :=
  inferInstanceAs (FiniteDimensional ℂ (X.obj ⟶ Y.obj))

def hasKernels : HasKernels (Positive χ) := S.fullSubcategoryHasKernels (positiveProperty χ)

def skeleton : FiniteSemisimpleSkeleton (Positive χ)
    {i : ι // positiveProperty χ (S.simpleObject i)} :=
  S.fullSubcategorySkeleton (positiveProperty χ)

variable [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [NatTrans.IsMonoidal χ.hom] [RightRigidCategory C] [Simple (𝟙_ C)]

def rightRigid : RightRigidCategory (Positive χ) := S.fullSubcategoryRightRigid (positiveProperty χ)

def simpleUnit : Simple (𝟙_ (Positive χ)) := S.fullSubcategorySimpleUnit (positiveProperty χ)

def pivotal (J : PivotalStructure C) :
    letI := rightRigid χ S
    PivotalStructure (Positive χ) := S.fullSubcategoryPivotal (positiveProperty χ) J

lemma pivotal_spherical (J : PivotalStructure C) (hJ : J.Spherical) :
    letI := rightRigid χ S
    (pivotal χ S J).Spherical :=
  S.fullSubcategoryPivotal_spherical (positiveProperty χ) J hJ

lemma inclusion_preservesPivotal (J : PivotalStructure C) :
    letI := rightRigid χ S
    PreservesPivotal (inclusion χ) (pivotal χ S J) J :=
  S.fullSubcategory_preservesPivotal (positiveProperty χ) J

end Semisimple
end Paper18.Category.SignKernel
