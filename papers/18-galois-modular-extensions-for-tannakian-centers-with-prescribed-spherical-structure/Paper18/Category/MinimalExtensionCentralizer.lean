import Paper18.Category.MinimalExtensionCentralizerBasic
import Paper18.Results.CategoricalProp22Minimal
import Paper18.Category.CentralizerDoubleDimension
import Paper18.Category.RelativeTensorCentralImage

/-! # The actual invertible centralizer in a minimal nondegenerate extension

Minimality computes the actual image-centralizer dimension. Its actual
two-simple support and the actual double-centralizer theorem then identify
the centralizer of the distinguished invertible with the actual essential image.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u' w'
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Braided] [F.Full] [F.Faithful]

/-- A fully faithful tensor functor preserves nonisomorphism to the unit. -/
lemma image_not_iso_unit {f : C} (hne : ¬ Nonempty (f ≅ 𝟙_ C)) :
    ¬ Nonempty (F.obj f ≅ 𝟙_ D) := by
  rintro ⟨e⟩
  exact hne ⟨F.preimageIso (e ≪≫ Functor.Monoidal.εIso F)⟩

/-- The actual centralizer of the distinguished invertible in a minimal
nondegenerate extension is exactly the actual essential image of the source. -/
theorem centralizer_invertible_eq_image_of_minimal (K : PivotalStructure D)
    (hD : IsNondegenerate (C := D))
    (hminimal : T.fusionBasis.totalFPdim = 2 * S.fusionBasis.totalFPdim)
    {f : C} (E : TensorInverse f) (hne : ¬ Nonempty (f ≅ 𝟙_ C))
    (hf : f ∈ mugerCenter (C := C)) :
    centralizer ({F.obj f} : Set D) = (F.essImage : Set D) := by
  have hfc : F.obj f ∈ centralizer (Set.range F.obj) := by
    rintro Y ⟨X, rfl⟩
    exact (hf X (Set.mem_univ _)).map F
  have hs := T.centralizer_eq_singleton_of_fpdim_two
    (centralizerProperty (Set.range F.obj)) (E.map F) (image_not_iso_unit F hne)
    (fun Y _ => centralizes_unit_left Y) hfc
    (centralizerFPdim_of_minimal S T F K hD hminimal)
  calc
    _ = centralizer (centralizer (Set.range F.obj)) := hs.symm
    _ = (F.essImage : Set D) := by
      have h := T.double_centralizer_eq K hD F.essImage
      rw [RelativeTensor.centralizer_essImage F] at h
      exact h

end Paper18.Category
