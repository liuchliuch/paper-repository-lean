import Paper18.Results.CategoricalProp22Boundary
import Paper18.Category.TwoObjectSupport
import Paper18.Category.RelativeCenterCentralizerDimension
import Paper18.Category.RelativeTensorCentralDimensionBasic

/-! # The spherical step for an actual minimal braided extension

The actual centralizer support is derived from minimality and the genuine
FP centralizer product. The remaining fixed-boundary morphism is exactly
the categorical conclusion to be constructed in Lemma A.1.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
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

/-- Actual minimality computes the actual centralizer dimension, without
receiving a centralizer-dimension identity as an input law. -/
lemma centralizerFPdim_of_minimal (K : PivotalStructure D)
    (hD : IsNondegenerate (C := D))
    (hminimal : T.fusionBasis.totalFPdim = 2 * S.fusionBasis.totalFPdim) :
    T.centralizerFPdim (Set.range F.obj) = 2 := by
  have h := T.supportFPdim_mul_centralizer K hD F.essImage
  have he : T.centralizerFPdim (F.essImage : Set D) =
      T.centralizerFPdim (Set.range F.obj) :=
    congrArg (fun q : Set D => T.supportFPdim (fun X => X ∈ q))
      (RelativeTensor.centralizer_essImage F)
  rw [RelativeTensor.supportFPdim_essImage S T F, he, hminimal] at h
  have hn : S.fusionBasis.totalFPdim ≠ 0 := by
    apply ne_of_gt
    exact Finset.sum_pos' (fun i _ => sq_nonneg (S.fusionBasis.fpdim i))
      ⟨S.fusionBasis.one, Finset.mem_univ _, pow_pos (S.fusionBasis.fpdim_pos _) _⟩
  apply mul_left_cancel₀ hn
  exact h.trans (mul_comm 2 _)

include S T in
/-- Every actual minimal nondegenerate extension is spherical once its
specified pivotal boundary is trivialized. The centralizer's two simple
objects are proved from actual minimality and the negative boson. -/
theorem spherical_of_minimal_pivotal_boundary
    (J : PivotalStructure C) (hJ : J.Spherical) (hD : IsNondegenerate (C := D))
    (hminimal : T.fusionBasis.totalFPdim = 2 * S.fusionBasis.totalFPdim)
    {f : C} (E : TensorInverse f) (he : f ⊗ f ≅ 𝟙_ C)
    (hf : (β_ f f).hom = 𝟙 (f ⊗ f)) (hdf : J.rightDim f = -1)
    (hc : f ∈ mugerCenter (C := C))
    (b : BoundaryIso F (pivotalBoundary F J) (BoundaryAutoequivalence.identity F)) :
    ∃ K : PivotalStructure D, K.Spherical ∧ PreservesPivotal F J K := by
  let K := pivotalOfBoundaryTrivialization F J b
  have hp : PreservesPivotal F J K := pivotalOfBoundaryTrivialization_preserves F J b
  have hdf' : K.rightDim (F.obj f) = -1 := (hp.rightDim_scalar f).trans hdf
  have hne : ¬ Nonempty (F.obj f ≅ 𝟙_ D) := by
    rintro ⟨a⟩
    have hdim := K.rightDim_iso a
    rw [K.rightDim_unit T, hdf'] at hdim
    norm_num at hdim
  have hfc : F.obj f ∈ centralizer (Set.range F.obj) := by
    intro Y hY
    obtain ⟨X,rfl⟩ := hY
    exact (hc X (Set.mem_univ X)).map F
  apply spherical_of_pivotal_boundary_trivialization S T F J hJ hD E he hf hdf
    (b := b)
  intro X hX hx
  letI := hX
  exact T.simple_support_of_fpdim_two (centralizerProperty (Set.range F.obj))
    (E.map F) hne (fun Y _ => centralizes_unit_left Y) hfc
    (centralizerFPdim_of_minimal S T F K hD hminimal) X hx

end Paper18.Category
