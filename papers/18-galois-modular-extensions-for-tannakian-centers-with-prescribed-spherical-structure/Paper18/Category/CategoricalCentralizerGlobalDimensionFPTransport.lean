import Paper18.Category.RelativeTensorCentralDimensionBasic
import Paper18.Category.CentralizerLatticeFPDimension

/-! # FP support transport along actual fully faithful tensor embeddings -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D] [Simple (𝟙_ D)]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  (F : C ⥤ D) [F.Monoidal] [F.Additive] [F.Linear ℂ]
  (Q : ObjectProperty D) [IsAdditiveFullProperty Q] [Q.IsMonoidal]

/-- The actual inverse-image fusion property of a tensor functor. -/
def dimensionPullbackProperty : ObjectProperty C := fun X => Q (F.obj X)

instance dimensionPullbackProperty_isAdditive : IsAdditiveFullProperty (dimensionPullbackProperty F Q) where
  of_retract r h := IsAdditiveFullProperty.of_retract (P := Q) (r.map F) h
  biproduct f h := IsAdditiveFullProperty.of_iso Q (F.mapBiproduct f)
    (IsAdditiveFullProperty.biproduct _ h)

instance dimensionPullbackProperty_isMonoidal : (dimensionPullbackProperty F Q).IsMonoidal where
  prop_unit := IsAdditiveFullProperty.of_iso Q (Functor.Monoidal.εIso F).symm (ObjectProperty.prop_unit Q)
  prop_tensor X Y hX hY := IsAdditiveFullProperty.of_iso Q (Functor.Monoidal.μIso F X Y).symm
    (ObjectProperty.prop_tensor hX hY)

variable {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  [F.Full] [F.Faithful]

/-- Actual essential-image intersection dimension equals the actual inverse
image support dimension. It is proved with the inherited source category
and the actual fully faithful composite tensor functor. -/
lemma supportFPdim_inter_essImage :
    T.supportFPdim (fun Y => F.essImage Y ∧ Q Y) =
      S.supportFPdim (dimensionPullbackProperty F Q) := by
  let P := dimensionPullbackProperty F Q
  letI := S.fullSubcategoryRightRigid P
  letI := S.fullSubcategoryHasKernels P
  letI := S.fullSubcategorySimpleUnit P
  let H := P.ι ⋙ F
  have he : H.essImage = (fun Y => F.essImage Y ∧ Q Y) := by
    funext Y
    apply propext
    constructor
    · rintro ⟨X, ⟨e⟩⟩
      exact ⟨⟨X.obj, ⟨e⟩⟩, IsAdditiveFullProperty.of_iso Q e.symm X.property⟩
    · rintro ⟨⟨X, ⟨e⟩⟩, hQ⟩
      exact ⟨⟨X, IsAdditiveFullProperty.of_iso Q e hQ⟩, ⟨e⟩⟩
  rw [← he, RelativeTensor.supportFPdim_essImage (S.fullSubcategorySkeleton P) T H,
    S.fullSubcategory_totalFPdim_eq P]

end Paper18.Category
