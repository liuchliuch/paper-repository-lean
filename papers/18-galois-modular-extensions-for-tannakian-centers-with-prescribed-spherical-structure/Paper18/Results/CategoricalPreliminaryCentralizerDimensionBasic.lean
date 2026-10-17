import Paper18.Category.SphericalizationCentralizerDimension
import Paper18.Category.SphericalizationEmbedding
import Paper18.Category.SphericalizationNegative
import Paper18.Category.SignKernelDimensions
import Paper18.Category.FixedBoundaryBosonGrading
import Paper18.Category.CentralizerDoubleDimension
import Paper18.Category.RelativeTensorCentralImage

/-! # Actual nontriviality and index two for the preliminary centralizer -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u'
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

namespace Sphericalized
variable {B : Type u'} [Category.{v'} B] [MonoidalCategory B]
  (F : B ⥤ C) [F.Monoidal] [F.Full] [F.Faithful]
  (Fhat : B ⥤ Sphericalized C) [Fhat.Monoidal]
  (e : Fhat ⋙ forget ≅ F)

include S e in
/-- The actual negative unit is outside every lift of a fully faithful
tensor functor. Forgetting an image isomorphism forces its source to be
the unit, contradicting the negative unit's proved nonisomorphism. -/
theorem negativeGenerator_not_mem_lift_image :
    ¬ Fhat.essImage (negativeGenerator (C := C)) := by
  rintro ⟨X, ⟨u⟩⟩
  let q : F.obj X ≅ F.obj (𝟙_ B) :=
    (e.app X).symm ≪≫ forget.mapIso u ≪≫ Functor.Monoidal.εIso F
  let v : X ≅ 𝟙_ B := F.preimageIso q
  exact negativeGenerator_not_iso_unit S
    ⟨u.symm ≪≫ Fhat.mapIso v ≪≫ (Functor.Monoidal.εIso Fhat).symm⟩

end Sphericalized
namespace PreliminaryCentralizer

section Image
variable {B : Type u'} [Category.{v'} B] [MonoidalCategory B]
  [Preadditive B] [HasFiniteBiproducts B] [HasKernels B]
  (G : B ⥤ C) [G.Monoidal] [G.Additive] [G.Full] [G.Faithful]

include S in
/-- In a genuinely nondegenerate extension, an object of the actual
image centralizer can be transparent there only if it belongs to the
original actual essential image. -/
theorem not_transparent_of_not_mem_image (J : PivotalStructure C)
    (hC : IsNondegenerate (C := C))
    (X : CentralizerCategory (Set.range G.obj))
    (hX : ¬ G.essImage X.obj) :
    X ∉ mugerCenter (C := CentralizerCategory (Set.range G.obj)) := by
  intro hz
  have hc : X.obj ∈ centralizer (centralizer (Set.range G.obj)) := by
    intro Y hY
    exact (hz ⟨Y, hY⟩ (Set.mem_univ _)).map
      (centralizerInclusion (Set.range G.obj))
  have hd := S.double_centralizer_eq J hC G.essImage
  rw [RelativeTensor.centralizer_essImage G] at hd
  exact hX (hd ▸ hc)

end Image

/-- A genuinely nontransparent order-two object gives a genuine index-two
centralizer. The index follows from its actual monodromy character and the
actual fusion multiplicities, without a pivotal structure. -/
theorem monodromy_indexTwo {f : C} (E : TensorInverse f)
    (q : f ⊗ f ≅ 𝟙_ C) (hf : f ∉ mugerCenter (C := C)) :
    S.fusionBasis.totalFPdim = 2 * S.centralizerFPdim {f} := by
  let χ := E.monodromyCharacter
  have hχ := E.monodromy_involutive_of_square q
  have hn : ∃ X : C, χ.hom.app X ≠ 𝟙 X := by
    by_contra h
    push_neg at h
    apply hf
    apply E.monodromyCharacter_eq_refl_iff.mp
    apply Iso.ext
    ext X
    exact h X
  obtain ⟨X, hX⟩ := hn
  have hp : SignKernel.positiveProperty χ = centralizerProperty ({f} : Set C) := by
    funext Y
    apply propext
    rw [SignKernel.mem_positive]
    constructor
    · intro h Z hZ
      rcases Set.mem_singleton_iff.mp hZ with rfl
      apply Centralizes.symm
      apply (E.monodromy_neutral_iff Y).mp
      simpa [FixedBoundary.Homogeneous, FixedBoundary.paritySign_zero] using h
    · intro h
      have hz := (E.monodromy_neutral_iff Y).mpr (h f (Set.mem_singleton f)).symm
      simpa [FixedBoundary.Homogeneous, FixedBoundary.paritySign_zero] using hz
  have hd := SignKernel.supportFPdim_indexTwo_of_nontrivial S χ hχ X hX
  rw [hp] at hd
  exact hd

end PreliminaryCentralizer
end Paper18.Category
