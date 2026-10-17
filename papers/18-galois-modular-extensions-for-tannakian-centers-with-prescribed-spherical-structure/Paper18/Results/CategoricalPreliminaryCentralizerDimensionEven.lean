import Paper18.Results.CategoricalPreliminaryCentralizerBasic
import Paper18.Results.CategoricalPreliminaryCentralizerDimensionBasic

/-! # The actual even centralizer dimension in a minimal extension -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category.PreliminaryCentralizer
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- The actual identity-on-underlying-objects nested centralizer equivalence
identifies intrinsic FP dimensions, using actual tensor equivalence. -/
theorem nestedCentralizerFPdim_eq (B : Set C) (e : CentralizerCategory B) :
    letI := S.fullSubcategoryHasKernels (centralizerProperty B)
    letI := S.fullSubcategoryRightRigid (centralizerProperty B)
    letI := S.fullSubcategorySimpleUnit (centralizerProperty B)
    (S.centralizerSkeleton B).centralizerFPdim {e} =
      S.centralizerFPdim (B ∪ {e.obj}) := by
  letI := S.fullSubcategoryHasKernels (centralizerProperty B)
  letI := S.fullSubcategoryRightRigid (centralizerProperty B)
  letI := S.fullSubcategorySimpleUnit (centralizerProperty B)
  let T := S.centralizerSkeleton B
  let P := centralizerProperty ({e} : Set (CentralizerCategory B))
  let Q := centralizerProperty (B ∪ {e.obj})
  letI := T.fullSubcategoryHasKernels P
  letI := T.fullSubcategoryRightRigid P
  letI := T.fullSubcategorySimpleUnit P
  letI := S.fullSubcategoryHasKernels Q
  letI := S.fullSubcategoryRightRigid Q
  letI := S.fullSubcategorySimpleUnit Q
  let E := CentralizerNested.equivalence B e
  letI : E.functor.Monoidal := (CentralizerNested.forward_braided B e).toMonoidal
  letI : E.functor.Additive := CentralizerNested.forward_additive B e
  letI : E.functor.Linear ℂ := CentralizerNested.forward_linear B e
  calc
    _ = (T.fullSubcategorySkeleton P).fusionBasis.totalFPdim :=
      (T.fullSubcategory_totalFPdim_eq P).symm
    _ = (S.fullSubcategorySkeleton Q).fusionBasis.totalFPdim :=
      RelativeTensor.totalFPdim_eq_of_equivalence
        (T.fullSubcategorySkeleton P) (S.fullSubcategorySkeleton Q) E.functor
    _ = _ := S.fullSubcategory_totalFPdim_eq Q

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (F : C ⥤ D) [F.Braided] [F.Additive] [F.Linear ℂ] [F.Full] [F.Faithful]
  (A : Set C) {f : C} (hf : f ∈ mugerCenter (C := C))

/-- In a genuine minimal extension, the even part of the actual preliminary
centralizer has the source centralizer dimension. The equality is derived
from the actual minimal-extension and nested-centralizer tensor equivalences. -/
theorem minimalCentralizer_evenFPdim (J : PivotalStructure D)
    (hD : IsNondegenerate (C := D))
    (hminimal : T.fusionBasis.totalFPdim = 2 * S.fusionBasis.totalFPdim)
    (E : TensorInverse f) (hne : ¬ Nonempty (f ≅ 𝟙_ C)) :
    letI := T.fullSubcategoryHasKernels (centralizerProperty (F.obj '' A))
    letI := T.fullSubcategoryRightRigid (centralizerProperty (F.obj '' A))
    letI := T.fullSubcategorySimpleUnit (centralizerProperty (F.obj '' A))
    (T.centralizerSkeleton (F.obj '' A)).centralizerFPdim
      {minimalCentralObject F A hf} = S.centralizerFPdim A := by
  letI := T.fullSubcategoryHasKernels (centralizerProperty (F.obj '' A))
  letI := T.fullSubcategoryRightRigid (centralizerProperty (F.obj '' A))
  letI := T.fullSubcategorySimpleUnit (centralizerProperty (F.obj '' A))
  rw [nestedCentralizerFPdim_eq T]
  let P := centralizerProperty A
  let Q := centralizerProperty (F.obj '' A ∪ {F.obj f})
  letI := S.fullSubcategoryHasKernels P
  letI := S.fullSubcategoryRightRigid P
  letI := S.fullSubcategorySimpleUnit P
  letI := T.fullSubcategoryHasKernels Q
  letI := T.fullSubcategoryRightRigid Q
  letI := T.fullSubcategorySimpleUnit Q
  let H := centralizerEquivalenceOfMinimal F A hf S T J hD hminimal E hne
  calc
    _ = (T.fullSubcategorySkeleton Q).fusionBasis.totalFPdim :=
      (T.fullSubcategory_totalFPdim_eq Q).symm
    _ = (S.fullSubcategorySkeleton P).fusionBasis.totalFPdim :=
      (RelativeTensor.totalFPdim_eq_of_equivalence
        (S.fullSubcategorySkeleton P) (T.fullSubcategorySkeleton Q) H.functor).symm
    _ = _ := S.fullSubcategory_totalFPdim_eq P

end Paper18.Category.PreliminaryCentralizer
