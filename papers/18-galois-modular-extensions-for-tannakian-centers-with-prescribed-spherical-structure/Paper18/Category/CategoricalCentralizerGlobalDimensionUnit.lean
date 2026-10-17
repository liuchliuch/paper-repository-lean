import Paper18.Category.CategoricalCentralizerGlobalDimensionSupport
import Paper18.Category.SphericalizationKernelTannakian
import Paper18.Category.SphericalizationEmbedding
import Paper18.Category.RelativeTensorCentralImage

/-! # The lifted positive image meets the transparent kernel only in units -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w v' u' w'
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C]
  [HasFiniteBiproducts C] [HasKernels C] [Simple (𝟙_ C)]

lemma simple_iso_unit_of_unitSum (X : C) [Simple X] (hX : IsUnitSum X) :
    Nonempty (X ≅ 𝟙_ C) := by
  obtain ⟨n, ⟨e⟩⟩ := hX
  let Q : Fin n → C := fun _ => 𝟙_ C
  have hn : ∃ a, biproduct.ι Q a ≫ e.inv ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : e.inv = 0 := by
      apply biproduct.hom_ext'
      intro a
      simpa using h a
    exact id_nonzero X (by rw [← e.hom_inv_id, hz, comp_zero])
  obtain ⟨a, ha⟩ := hn
  letI : IsIso (biproduct.ι Q a ≫ e.inv) := isIso_of_mono_of_nonzero ha
  exact ⟨(asIso (biproduct.ι Q a ≫ e.inv)).symm⟩

variable [MonoidalLinear ℂ C] [RightRigidCategory C] [BraidedCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι]
namespace FiniteSemisimpleSkeleton
variable (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

lemma supportGlobalDimension_eq_one_of_unit_support (P : ObjectProperty C)
    (hunit : P (S.simpleObject S.unitLabel))
    (h : ∀ i, P (S.simpleObject i) → Nonempty (S.simpleObject i ≅ 𝟙_ C)) :
    S.supportGlobalDimension J P = 1 := by
  have he (i : ι) : P (S.simpleObject i) ↔ i = S.unitLabel := by
    refine ⟨fun hi => S.iso_injective i S.unitLabel ?_, ?_⟩
    · exact (h i hi).map (fun e => e ≪≫ S.unitIso.symm)
    · rintro rfl
      exact hunit
  simp only [supportGlobalDimension, he]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact (J.pivotalData S).ndim_one

lemma supportFPdim_eq_one_of_unit_support (P : ObjectProperty C)
    (hunit : P (S.simpleObject S.unitLabel))
    (h : ∀ i, P (S.simpleObject i) → Nonempty (S.simpleObject i ≅ 𝟙_ C)) :
    S.supportFPdim P = 1 := by
  have he (i : ι) : P (S.simpleObject i) ↔ i = S.unitLabel := by
    refine ⟨fun hi => S.iso_injective i S.unitLabel ?_, ?_⟩
    · exact (h i hi).map (fun e => e ≪≫ S.unitIso.symm)
    · rintro rfl
      exact hunit
  simp only [supportFPdim, he]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hu : S.fusionBasis.fpdim S.unitLabel = 1 := S.fusionBasis.fpdim_one
  rw [hu]
  norm_num

end FiniteSemisimpleSkeleton
namespace Sphericalized
variable {B : Type u'} [Category.{v'} B] [MonoidalCategory B] [RightRigidCategory B]
  [Preadditive B] [Linear ℂ B] [MonoidalPreadditive B] [MonoidalLinear ℂ B]
  [HasKernels B] [HasFiniteBiproducts B] [Simple (𝟙_ B)] [BraidedCategory B]
  [∀ X Y : B, FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton B κ)
  (J : PivotalStructure B) (hJ : J.Spherical)
  (F : B ⥤ C) [F.Braided] [F.Additive] [F.Linear ℂ] [F.Full] [F.Faithful]

lemma unitSum_of_embedding_and_transparent (hC : IsNondegenerate (C := C))
    (X : Sphericalized C) (hX : (embedding T J hJ F).essImage X)
    (hZ : X ∈ mugerCenter) : IsUnitSum X := by
  obtain ⟨Y, ⟨e⟩⟩ := hX
  have hu : IsUnitSum (F.obj Y) :=
    IsUnitSum.of_iso ((forget (C := C)).mapIso e)
      ((transparent_iff_kernel hC X).mp hZ)
  exact IsUnitSum.of_iso e.symm
    (RelativeTensor.unitSum_map (embedding T J hJ F) (RelativeTensor.unitSum_of_map F hu))

lemma embedding_transparent_globalDimension (S : FiniteSemisimpleSkeleton C ι)
    (hC : IsNondegenerate (C := C)) :
    (skeleton S).supportGlobalDimension pivotalStructure
      (fun X => (embedding T J hJ F).essImage X ∧ X ∈ mugerCenter) = 1 := by
  let H := embedding T J hJ F
  apply (skeleton S).supportGlobalDimension_eq_one_of_unit_support pivotalStructure
  · constructor
    · exact IsAdditiveFullProperty.of_iso H.essImage (skeleton S).unitIso (ObjectProperty.prop_unit H.essImage)
    · exact unitSum_mem_mugerCenter
        (IsUnitSum.of_iso (skeleton S).unitIso IsUnitSum.unit)
  · intro i hi
    exact simple_iso_unit_of_unitSum _
      (unitSum_of_embedding_and_transparent T J hJ F hC _ hi.1 hi.2)

lemma embedding_transparent_FPdim (S : FiniteSemisimpleSkeleton C ι)
    (hC : IsNondegenerate (C := C)) :
    (skeleton S).supportFPdim
      (fun X => (embedding T J hJ F).essImage X ∧ X ∈ mugerCenter) = 1 := by
  let H := embedding T J hJ F
  apply (skeleton S).supportFPdim_eq_one_of_unit_support
  · constructor
    · exact IsAdditiveFullProperty.of_iso H.essImage (skeleton S).unitIso (ObjectProperty.prop_unit H.essImage)
    · exact unitSum_mem_mugerCenter
        (IsUnitSum.of_iso (skeleton S).unitIso IsUnitSum.unit)
  · intro i hi
    exact simple_iso_unit_of_unitSum _
      (unitSum_of_embedding_and_transparent T J hJ F hC _ hi.1 hi.2)

end Sphericalized
end Paper18.Category
