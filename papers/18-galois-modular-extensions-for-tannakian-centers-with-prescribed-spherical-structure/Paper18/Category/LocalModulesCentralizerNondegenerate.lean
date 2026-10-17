import Paper18.Category.RelativeTensorCentralImage
import Paper18.Category.CentralizerDoubleDimension

/-! # Nondegeneracy of actual centralizers of nondegenerate braided images -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u v' u' w'
namespace Paper18.Category.RelativeTensor
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  [HasKernels C] [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)] [BraidedCategory D]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (JD : PivotalStructure D) (F : C ⥤ D) [F.Additive] [F.Braided] [F.Full] [F.Faithful]
include T JD

omit [MonoidalPreadditive C] in
/-- The actual centralizer of a fully faithful nondegenerate braided image
is nondegenerate. The double-centralizer identity is derived from the
actual ambient fusion category, rather than supplied as a premise. -/
theorem centralizerImage_nondegenerate (hD : IsNondegenerate (C := D))
    (hC : IsNondegenerate (C := C)) :
    IsNondegenerate (C := CentralizerCategory (Set.range F.obj)) := by
  intro X hX
  have hdouble : centralizer (centralizer (Set.range F.obj)) = (F.essImage : Set D) := by
    have h := T.double_centralizer_eq JD hD F.essImage
    rw [centralizer_essImage F] at h
    exact h
  have hXX : X.obj ∈ centralizer (centralizer (Set.range F.obj)) := by
    intro Y hY
    exact hX (⟨Y, hY⟩ : CentralizerCategory (Set.range F.obj)) (Set.mem_univ _)
  have himage : F.essImage X.obj := by
    rw [← hdouble]
    exact hXX
  exact unitSum_fullSubcategory (centralizerProperty (Set.range F.obj)) X
    (unitSum_of_image_and_centralizer F hC himage X.property)

end Paper18.Category.RelativeTensor
