import Paper18.Category.SphericalizationKernel
import Paper18.Category.TannakianBasic

/-! # Actual Tannakian center of sphericalization over a nondegenerate category -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.Sphericalized
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [CategoryTheory.Limits.HasFiniteBiproducts C] [CategoryTheory.Limits.HasKernels C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]

omit [MonoidalLinear ℂ C] [CategoryTheory.Limits.HasKernels C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)] in
lemma kernelProperty_transparent (X : Sphericalized C) (hX : kernelProperty X) :
    X ∈ mugerCenter := by
  intro Y _
  exact (centralizes_map_iff (forget (C := C)) X Y).mp
    (unitSum_mem_mugerCenter hX Y.obj.obj (Set.mem_univ _))

/-- Nondegeneracy of the original category forces every transparent square
object into the actual forgetful kernel, using proved retract dominance. -/
lemma transparent_iff_kernel (hC : IsNondegenerate (C := C)) (X : Sphericalized C) :
    X ∈ mugerCenter ↔ kernelProperty X := by
  constructor
  · intro hX
    apply hC
    intro Y _
    obtain ⟨Z, ⟨r⟩⟩ := forget_retract_dominant (C := C) Y
    exact ((hX Z (Set.mem_univ _)).map (forget (C := C))).of_retract_right r
  · exact kernelProperty_transparent X

def kernelRepInclusion : FDRep ℂ RepresentationZ2.H ⥤ Sphericalized C :=
  (kernelEquivalence (C := C)).inverse ⋙ kernelInclusion

instance kernelRepInclusion_braided : (kernelRepInclusion (C := C)).Braided := by
  dsimp [kernelRepInclusion]; infer_instance
instance kernelRepInclusion_additive : (kernelRepInclusion (C := C)).Additive := by
  dsimp [kernelRepInclusion, kernelInclusion]; infer_instance
instance kernelRepInclusion_linear : (kernelRepInclusion (C := C)).Linear ℂ := by
  dsimp [kernelRepInclusion, kernelInclusion]; infer_instance
instance kernelRepInclusion_full : (kernelRepInclusion (C := C)).Full := by
  dsimp [kernelRepInclusion, kernelInclusion]; infer_instance
instance kernelRepInclusion_faithful : (kernelRepInclusion (C := C)).Faithful := by
  dsimp [kernelRepInclusion, kernelInclusion]; infer_instance

lemma kernelRepInclusion_image_iff (X : Sphericalized C) :
    (kernelRepInclusion (C := C)).essImage X ↔ kernelProperty X := by
  constructor
  · rintro ⟨V, ⟨e⟩⟩
    exact IsUnitSum.of_iso ((forget (C := C)).mapIso e.symm)
      (((kernelEquivalence (C := C)).inverse.obj V).property)
  · intro hX
    let Z : Kernel (C := C) := ⟨X, hX⟩
    exact ⟨(kernelEquivalence (C := C)).functor.obj Z,
      ⟨kernelInclusion.mapIso ((kernelEquivalence (C := C)).unitIso.app Z).symm⟩⟩

/-- The actual transparent center of sphericalization is Rep(C₂) whenever
the original actual braided category is nondegenerate. -/
def tannakianCenter (hC : IsNondegenerate (C := C)) :
    TannakianCenter (Sphericalized C) RepresentationZ2.H where
  finite_group := inferInstance
  inclusion := kernelRepInclusion
  braided := kernelRepInclusion_braided
  additive := kernelRepInclusion_additive
  linear := kernelRepInclusion_linear
  full := kernelRepInclusion_full
  faithful := kernelRepInclusion_faithful
  image_iff X := (kernelRepInclusion_image_iff X).trans (transparent_iff_kernel hC X).symm

end Paper18.Category.Sphericalized
