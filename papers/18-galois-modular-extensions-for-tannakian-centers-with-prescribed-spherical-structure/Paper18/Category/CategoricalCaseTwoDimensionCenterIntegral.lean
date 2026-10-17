import Paper18.Category.CategoricalCaseTwoDimensionCenter
import Paper18.Category.FusionJoinIntegralImage

/-! # Actual integrality of the ambient image of the transparent center -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe vN uN wN vB uB
namespace Paper18.Category.CategoricalCaseTwo
variable {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [HasFiniteBiproducts N]
  {B : Type uB} [Category.{vB} B] (H : B ⥤ N)

/-- The actual inclusion of the actual centralizer's transparent center
into the ambient category. -/
def centerAmbientInclusion :
    CentralizerCategory (Set.univ : Set (CentralizerCategory (Set.range H.obj))) ⥤ N :=
  centralizerInclusion Set.univ ⋙ centralizerInclusion (Set.range H.obj)

instance centerAmbientInclusion_additive : (centerAmbientInclusion H).Additive := by
  unfold centerAmbientInclusion; infer_instance
instance centerAmbientInclusion_linear : (centerAmbientInclusion H).Linear ℂ := by
  unfold centerAmbientInclusion; infer_instance
instance centerAmbientInclusion_braided : (centerAmbientInclusion H).Braided := by
  unfold centerAmbientInclusion; infer_instance
instance centerAmbientInclusion_full : (centerAmbientInclusion H).Full := by
  unfold centerAmbientInclusion; infer_instance
instance centerAmbientInclusion_faithful : (centerAmbientInclusion H).Faithful := by
  unfold centerAmbientInclusion; infer_instance

/-- The actual essential image is exactly the ambient center property
used by the local free embedding. Both directions exhibit actual objects
and actual isomorphisms. -/
lemma centerAmbientInclusion_essImage :
    (centerAmbientInclusion H).essImage = ambientCenterProperty H := by
  funext X
  apply propext
  constructor
  · rintro ⟨Z,⟨e⟩⟩
    have hz : ambientCenterProperty H Z.obj.obj :=
      (ambientCenterProperty_inclusion_iff H Z.obj).mpr Z.property
    exact @IsAdditiveFullProperty.of_iso N _ _ ‹HasFiniteBiproducts N›
      (ambientCenterProperty H) _ _ _ e.symm hz
  · intro h
    let Y : CentralizerCategory (Set.range H.obj) := ⟨X,h.1⟩
    let Z : CentralizerCategory (Set.univ : Set (CentralizerCategory (Set.range H.obj))) :=
      ⟨Y,(ambientCenterProperty_inclusion_iff H Y).mp h⟩
    exact ⟨Z,⟨Iso.refl X⟩⟩

variable [HasKernels N] [RightRigidCategory N] [Simple (𝟙_ N)]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  {ιN : Type wN} [Fintype ιN] (SN : FiniteSemisimpleSkeleton N ιN)

/-- Integrality of the actual transparent center transports to its actual
ambient full image through the proved fully faithful tensor inclusion. -/
lemma ambientCenter_integral :
    (letI := SN.fullSubcategoryHasKernels (centralizerProperty (Set.range H.obj))
     letI := SN.fullSubcategoryRightRigid (centralizerProperty (Set.range H.obj))
     letI := SN.fullSubcategorySimpleUnit (centralizerProperty (Set.range H.obj))
     (SN.centralizerSkeleton (Set.range H.obj)).CentralizerIntegral Set.univ) →
       SN.FullSubcategoryIntegral (ambientCenterProperty H) := by
  letI := SN.fullSubcategoryHasKernels (centralizerProperty (Set.range H.obj))
  letI := SN.fullSubcategoryRightRigid (centralizerProperty (Set.range H.obj))
  letI := SN.fullSubcategorySimpleUnit (centralizerProperty (Set.range H.obj))
  let SK := SN.centralizerSkeleton (Set.range H.obj)
  letI := SK.fullSubcategoryHasKernels (centralizerProperty Set.univ)
  letI := SK.fullSubcategoryRightRigid (centralizerProperty Set.univ)
  letI := SK.fullSubcategorySimpleUnit (centralizerProperty Set.univ)
  let SE := SK.centralizerSkeleton Set.univ
  intro hE
  change SE.Integral at hE
  have h := SE.essImageIntegral SN (centerAmbientInclusion H) hE
  apply (SN.fullSubcategoryIntegral_iff (ambientCenterProperty H)).mpr
  intro i hi
  apply (SN.fullSubcategoryIntegral_iff (centerAmbientInclusion H).essImage).mp h i
  rw [centerAmbientInclusion_essImage]
  exact hi

end Paper18.Category.CategoricalCaseTwo
