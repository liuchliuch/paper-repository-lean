import Paper18.Category.MinimalExtensionCentralizerEquivalence
import Paper18.Category.CentralizerNested
import Paper18.Category.MonodromyWeakIntegrality
import Paper18.Category.ModuleBalancingPositive

/-! # The actual preliminary centralizer and its order-two object

The central object is the image of the actual transparent source object.
Its tensor square and inverse are constructed in the actual full centralizer.
Minimality transfers the integral simultaneous centralizer; the genuine
monodromy grading then proves weak integrality of the preliminary category.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open Functor.Monoidal
universe v u w v' u' w'
namespace Paper18.Category.PreliminaryCentralizer
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  (F : C ⥤ D) [F.Braided] (A : Set C) {f : C}
  (hf : f ∈ mugerCenter (C := C))

/-- The source's actual transparent object, inside the actual centralizer
of the image of the specified source objects. -/
def minimalCentralObject : CentralizerCategory (F.obj '' A) :=
  ⟨F.obj f, by
    rintro Y ⟨X, _, rfl⟩
    exact (hf X (Set.mem_univ X)).map F⟩

@[simp] lemma minimalCentralObject_obj :
    (minimalCentralObject F A hf).obj = F.obj f := rfl

/-- The actual image tensor comparison transports the order-two square. -/
def minimalCentralSquareIso (q : f ⊗ f ≅ 𝟙_ C) :
    minimalCentralObject F A hf ⊗ minimalCentralObject F A hf ≅
      𝟙_ (CentralizerCategory (F.obj '' A)) :=
  (centralizerProperty (F.obj '' A)).isoMk
    (μIso F f f ≪≫ F.mapIso q ≪≫ (εIso F).symm)

/-- In the centralizer the actual order-two object is its own two-sided inverse. -/
def minimalCentralTensorInverse (q : f ⊗ f ≅ 𝟙_ C) :
    TensorInverse (minimalCentralObject F A hf) where
  inverse := minimalCentralObject F A hf
  left := minimalCentralSquareIso F A hf q
  right := minimalCentralSquareIso F A hf q

/-- The actual image object retains a trivial self-braiding. -/
lemma minimalCentralObject_selfBraiding
    (hff : (β_ f f).hom = 𝟙 (f ⊗ f)) :
    (β_ (minimalCentralObject F A hf) (minimalCentralObject F A hf)).hom =
      𝟙 (minimalCentralObject F A hf ⊗ minimalCentralObject F A hf) := by
  apply (centralizerInclusion (F.obj '' A)).map_injective
  change (β_ (F.obj f) (F.obj f)).hom = 𝟙 _
  apply (cancel_mono (Functor.LaxMonoidal.μ F f f)).mp
  rw [← Functor.LaxBraided.braided, hff, F.map_id]
  simp

/-- Full faithfulness reflects nontriviality of the actual distinguished object. -/
lemma minimalCentralObject_not_iso_unit [F.Full] [F.Faithful]
    (hne : ¬ Nonempty (f ≅ 𝟙_ C)) :
    ¬ Nonempty (minimalCentralObject F A hf ≅ 𝟙_ (CentralizerCategory (F.obj '' A))) := by
  rintro ⟨a⟩
  exact hne ⟨F.preimageIso
    ((centralizerInclusion (F.obj '' A)).mapIso a ≪≫ εIso F)⟩

section Fusion
variable [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  [F.Additive] [F.Linear ℂ] [F.Full] [F.Faithful]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)

/-- The even part of the actual preliminary centralizer is integral,
by the proved minimal-extension equivalence and the actual nested centralizer. -/
theorem minimalCentralizer_evenIntegral (J : PivotalStructure D)
    (hD : IsNondegenerate (C := D))
    (hminimal : T.fusionBasis.totalFPdim = 2 * S.fusionBasis.totalFPdim)
    (E : TensorInverse f) (hne : ¬ Nonempty (f ≅ 𝟙_ C))
    (hI : S.CentralizerIntegral A) :
    letI := T.fullSubcategoryHasKernels (centralizerProperty (F.obj '' A))
    letI := T.fullSubcategoryRightRigid (centralizerProperty (F.obj '' A))
    letI := T.fullSubcategorySimpleUnit (centralizerProperty (F.obj '' A))
    (T.centralizerSkeleton (F.obj '' A)).CentralizerIntegral
      {minimalCentralObject F A hf} := by
  exact CentralizerNested.integral_of_ambient_union_integral
    (F.obj '' A) (minimalCentralObject F A hf) T
    (centralizerIntegral_image_union_of_minimal F A hf S T J hD hminimal E hne hI)

include hf in
/-- An integral even part makes the actual preliminary category weakly
integral. No pivotal structure on the source category is assumed. -/
theorem minimalCentralizer_weaklyIntegral (J : PivotalStructure D)
    (hD : IsNondegenerate (C := D))
    (hminimal : T.fusionBasis.totalFPdim = 2 * S.fusionBasis.totalFPdim)
    (E : TensorInverse f) (q : f ⊗ f ≅ 𝟙_ C)
    (hne : ¬ Nonempty (f ≅ 𝟙_ C)) (hI : S.CentralizerIntegral A) :
    letI := T.fullSubcategoryHasKernels (centralizerProperty (F.obj '' A))
    letI := T.fullSubcategoryRightRigid (centralizerProperty (F.obj '' A))
    letI := T.fullSubcategorySimpleUnit (centralizerProperty (F.obj '' A))
    (T.centralizerSkeleton (F.obj '' A)).fusionBasis.WeaklyIntegral := by
  letI := T.fullSubcategoryHasKernels (centralizerProperty (F.obj '' A))
  letI := T.fullSubcategoryRightRigid (centralizerProperty (F.obj '' A))
  letI := T.fullSubcategorySimpleUnit (centralizerProperty (F.obj '' A))
  exact (T.centralizerSkeleton (F.obj '' A)).weaklyIntegral_of_orderTwo_centralizerIntegral
    (minimalCentralTensorInverse F A hf q) (minimalCentralSquareIso F A hf q)
    (minimalCentralizer_evenIntegral F A hf S T J hD hminimal E hne hI)

/-- The inherited pivotal dimension of the actual centralizer object is
the source dimension, using the actual canonical dual comparisons. -/
lemma minimalCentralObject_rightDim (J : PivotalStructure C) (K : PivotalStructure D)
    (hp : PreservesPivotal F J K) :
    letI := T.fullSubcategoryHasKernels (centralizerProperty (F.obj '' A))
    letI := T.fullSubcategoryRightRigid (centralizerProperty (F.obj '' A))
    letI := T.fullSubcategorySimpleUnit (centralizerProperty (F.obj '' A))
    (T.centralizerPivotal (F.obj '' A) K).rightDim (minimalCentralObject F A hf) =
      J.rightDim f := by
  letI := T.fullSubcategoryHasKernels (centralizerProperty (F.obj '' A))
  letI := T.fullSubcategoryRightRigid (centralizerProperty (F.obj '' A))
  letI := T.fullSubcategorySimpleUnit (centralizerProperty (F.obj '' A))
  rw [← (T.fullSubcategory_preservesPivotal (centralizerProperty (F.obj '' A)) K).rightDim_scalar]
  exact hp.rightDim_scalar f

end Fusion
end Paper18.Category.PreliminaryCentralizer
