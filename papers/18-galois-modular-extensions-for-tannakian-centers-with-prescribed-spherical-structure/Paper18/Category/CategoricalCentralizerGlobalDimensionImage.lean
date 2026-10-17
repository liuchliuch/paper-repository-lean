import Paper18.Category.CategoricalCentralizerGlobalDimensionSupport
import Paper18.Category.RelativeTensorCentralDimensionBasic

/-! # Actual positive tensor images have their intrinsic squared dimension -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w v' u' w'
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D] [Simple (𝟙_ D)] [BraidedCategory D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (F : C ⥤ D) [F.Monoidal] [F.Additive] [F.Linear ℂ] [F.Full] [F.Faithful]
  (J : PivotalStructure C) (K : PivotalStructure D)

lemma supportGlobalDimension_essImage_of_positive
    (hF : PreservesPivotal F J K) (hJ : J.Positive) :
    T.supportGlobalDimension K F.essImage = (S.fusionBasis.totalFPdim : ℂ) := by
  have he : T.supportGlobalDimension K F.essImage = (T.supportFPdim F.essImage : ℂ) := by
    simp only [FiniteSemisimpleSkeleton.supportGlobalDimension,
      FiniteSemisimpleSkeleton.supportFPdim, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : F.essImage (T.simpleObject i)
    · rw [if_pos hi, if_pos hi, Paper18.PivotalData.ndim_eq_normSq]
      obtain ⟨Y, ⟨e⟩⟩ := hi
      have hd : K.rightDim (T.simpleObject i) = (T.fusionBasis.fpdim i : ℂ) := by
        rw [← K.rightDim_iso e, hF.rightDim_scalar, J.rightDim_eq_fpdim S hJ,
          ← S.fpdim_map T F, T.fpdim_iso e, T.fpdim_simple]
      change (Complex.normSq (K.rightDim (T.simpleObject i)) : ℂ) = _
      rw [hd, Complex.normSq_ofReal]
      push_cast
      ring
    · simp only [if_neg hi, Complex.ofReal_zero]
  rw [he, RelativeTensor.supportFPdim_essImage S T F]

end Paper18.Category
