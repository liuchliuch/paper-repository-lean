import Paper18.Category.CategoricalCaseTwoDimensionBasic
import Paper18.Category.RelativeTensorCentralDimensionBasic
import Paper18.Category.DiagonalCondensationIntersectionCentralizer

/-! # The actual ambient center and its positive common part in Case 2 -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe vN uN wN vB uB
namespace Paper18.Category.CategoricalCaseTwo
variable {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [HasFiniteBiproducts N]
  {B : Type uB} [Category.{vB} B] (H : B ⥤ N)

/-- The actual transparent center of the actual ambient centralizer,
regarded as an actual full subcategory of the ambient category. -/
def ambientCenterProperty : ObjectProperty N := fun X =>
  X ∈ centralizer (Set.range H.obj) ∧
    X ∈ centralizer (Set.range (centralizerInclusion (Set.range H.obj)).obj)

instance ambientCenterProperty_monoidal : (ambientCenterProperty H).IsMonoidal where
  prop_unit := ⟨ObjectProperty.prop_unit (centralizerProperty _),
    ObjectProperty.prop_unit (centralizerProperty _)⟩
  prop_tensor _ _ hX hY := ⟨centralizer_tensor hX.1 hY.1, centralizer_tensor hX.2 hY.2⟩

instance ambientCenterProperty_additive : IsAdditiveFullProperty (ambientCenterProperty H) where
  of_retract r hY := ⟨centralizer_retract r hY.1, centralizer_retract r hY.2⟩
  biproduct f hf := ⟨centralizer_biproduct f (fun j => (hf j).1),
    centralizer_biproduct f (fun j => (hf j).2)⟩

/-- Actual braided faithfulness of the centralizer inclusion identifies
transparency with ambient centralization of all actual centralizer objects. -/
lemma centralizer_transparent_iff (X : CentralizerCategory (Set.range H.obj)) :
    X ∈ mugerCenter ↔ X.obj ∈ centralizer
      (Set.range (centralizerInclusion (Set.range H.obj)).obj) := by
  constructor
  · intro h Y hY
    obtain ⟨Y,rfl⟩ := hY
    exact (h Y (Set.mem_univ _)).map (centralizerInclusion (Set.range H.obj))
  · intro h Y _
    exact (centralizes_map_iff (centralizerInclusion (Set.range H.obj)) X Y).mp
      (h Y.obj ⟨Y,rfl⟩)

lemma ambientCenterProperty_inclusion_iff (X : CentralizerCategory (Set.range H.obj)) :
    ambientCenterProperty H X.obj ↔ X ∈ mugerCenter := by
  exact ⟨fun h => (centralizer_transparent_iff H X).mpr h.2,
    fun h => ⟨X.property,(centralizer_transparent_iff H X).mp h⟩⟩

variable (χ : 𝟭 (CentralizerCategory (Set.range H.obj)) ≅ 𝟭 (CentralizerCategory (Set.range H.obj)))
  [NatTrans.IsMonoidal χ.hom]

/-- The actual positive-kernel inclusion into the original ambient category. -/
def positiveAmbientInclusion : SignKernel.Positive χ ⥤ N :=
  SignKernel.inclusion χ ⋙ centralizerInclusion (Set.range H.obj)

instance positiveAmbientInclusion_additive : (positiveAmbientInclusion H χ).Additive := by
  unfold positiveAmbientInclusion; infer_instance
instance positiveAmbientInclusion_linear : (positiveAmbientInclusion H χ).Linear ℂ := by
  unfold positiveAmbientInclusion; infer_instance
instance positiveAmbientInclusion_braided : (positiveAmbientInclusion H χ).Braided := by
  unfold positiveAmbientInclusion; infer_instance
instance positiveAmbientInclusion_full : (positiveAmbientInclusion H χ).Full := by
  unfold positiveAmbientInclusion; infer_instance
instance positiveAmbientInclusion_faithful : (positiveAmbientInclusion H χ).Faithful := by
  unfold positiveAmbientInclusion; infer_instance

/-- The actual common part is exactly the positive objects whose actual
underlying centralizer objects are transparent. -/
lemma positive_commonPart_iff (X : SignKernel.Positive χ) :
    DiagonalCondensation.commonPartProperty (positiveAmbientInclusion H χ)
      (ambientCenterProperty H) X ↔ X.obj ∈ mugerCenter :=
  ambientCenterProperty_inclusion_iff H X.obj

lemma positive_centralizes_ambient_center (Y : SignKernel.Positive χ)
    (X : (ambientCenterProperty H).FullSubcategory) :
    Centralizes ((positiveAmbientInclusion H χ).obj Y) X.obj :=
  (X.property.2 _ ⟨Y.obj,rfl⟩).symm

lemma positive_centralizes_original (Y : SignKernel.Positive χ) (X : B) :
    Centralizes ((positiveAmbientInclusion H χ).obj Y) (H.obj X) :=
  Y.obj.property _ ⟨X,rfl⟩

variable [HasKernels N] [RightRigidCategory N] [Simple (𝟙_ N)]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  {ιN : Type wN} [Fintype ιN] (SN : FiniteSemisimpleSkeleton N ιN)

/-- The first generator has precisely the intrinsic FP dimension of the
actual transparent center of the actual ambient centralizer. -/
lemma ambientCenterFPdim :
    (letI := SN.fullSubcategoryHasKernels (centralizerProperty (Set.range H.obj))
     letI := SN.fullSubcategoryRightRigid (centralizerProperty (Set.range H.obj))
     letI := SN.fullSubcategorySimpleUnit (centralizerProperty (Set.range H.obj))
     (SN.centralizerSkeleton (Set.range H.obj)).centralizerFPdim
       (Set.univ : Set (CentralizerCategory (Set.range H.obj)))) =
      SN.supportFPdim (ambientCenterProperty H) := by
  letI := SN.fullSubcategoryHasKernels (centralizerProperty (Set.range H.obj))
  letI := SN.fullSubcategoryRightRigid (centralizerProperty (Set.range H.obj))
  letI := SN.fullSubcategorySimpleUnit (centralizerProperty (Set.range H.obj))
  let SK := SN.centralizerSkeleton (Set.range H.obj)
  have he : centralizerProperty (Set.univ : Set (CentralizerCategory (Set.range H.obj))) =
      (fun X => X.obj ∈ centralizer
        (Set.range (centralizerInclusion (Set.range H.obj)).obj)) := by
    funext X
    exact propext (centralizer_transparent_iff H X)
  change SK.supportFPdim (centralizerProperty Set.univ) = _
  rw [he]
  exact SignKernel.fullSubcategory_supportFPdim_eq SN
    (centralizerProperty (Set.range H.obj))
    (centralizerProperty (Set.range (centralizerInclusion (Set.range H.obj)).obj))

include SN in
/-- The actual shared-source subcategory detected by the two local free
images has the actual positive-center dimension. Transparency of the
positive kernel is identified categorically, using the nontrivial central
character, before its FP dimension is computed. -/
lemma positive_commonPartFPdim
    (hχ : ∀ X, χ.hom.app X ≫ χ.hom.app X = 𝟙 X)
    (X : CentralizerCategory (Set.range H.obj))
    (hZ : X ∈ mugerCenter) (hX : χ.hom.app X ≠ 𝟙 X) :
    letI := SN.fullSubcategoryHasKernels (centralizerProperty (Set.range H.obj))
    letI := SN.fullSubcategoryRightRigid (centralizerProperty (Set.range H.obj))
    letI := SN.fullSubcategorySimpleUnit (centralizerProperty (Set.range H.obj))
    let SK := SN.centralizerSkeleton (Set.range H.obj)
    letI := SignKernel.hasKernels χ SK
    letI := SignKernel.rightRigid χ SK
    letI := SignKernel.simpleUnit χ SK
    (SignKernel.skeleton χ SK).supportFPdim
      (DiagonalCondensation.commonPartProperty (positiveAmbientInclusion H χ) (ambientCenterProperty H)) =
        SignKernel.positiveCenterFPdim SK χ := by
  letI := SN.fullSubcategoryHasKernels (centralizerProperty (Set.range H.obj))
  letI := SN.fullSubcategoryRightRigid (centralizerProperty (Set.range H.obj))
  letI := SN.fullSubcategorySimpleUnit (centralizerProperty (Set.range H.obj))
  let SK := SN.centralizerSkeleton (Set.range H.obj)
  letI := SignKernel.hasKernels χ SK
  letI := SignKernel.rightRigid χ SK
  letI := SignKernel.simpleUnit χ SK
  have he : DiagonalCondensation.commonPartProperty (positiveAmbientInclusion H χ)
      (ambientCenterProperty H) =
      centralizerProperty (Set.univ : Set (SignKernel.Positive χ)) := by
    funext Y
    exact propext ((positive_commonPart_iff H χ Y).trans
      (SignKernel.transparent_iff_ambient_of_nontrivial_center χ SK hχ X hZ hX Y).symm)
  rw [he]
  rfl

end Paper18.Category.CategoricalCaseTwo
