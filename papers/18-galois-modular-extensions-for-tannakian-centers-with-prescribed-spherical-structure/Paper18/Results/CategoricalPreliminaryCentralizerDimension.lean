import Paper18.Results.CategoricalPreliminaryCentralizerDimensionEven
import Paper18.Results.CategoricalPreliminaryCentralizerSphericalized

/-! # The actual preliminary dimension formula (3.3)

The original target has no pivotal structure. The actual negative unit is
outside the prescribed lift's essential image, so the genuine double
centralizer in the nondegenerate extension forces nontrivial monodromy in
the preliminary centralizer. Its actual even part is identified by tensor
equivalences, and the two proved index-two formulas give the factor four.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u' w' v'' u'' w''
namespace Paper18.Category.PreliminaryCentralizer
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {B : Type u'} [Category.{v'} B] [MonoidalCategory B] [BraidedCategory B]
  [RightRigidCategory B] [Preadditive B] [Linear ℂ B]
  [MonoidalPreadditive B] [MonoidalLinear ℂ B] [HasKernels B] [HasFiniteBiproducts B]
  [∀ X Y : B, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ B)]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton B κ)
  (JB : PivotalStructure B) (hJB : JB.Spherical)
  (F : B ⥤ C) [F.Braided] [F.Additive] [F.Linear ℂ] [F.Full] [F.Faithful]
  {N : Type u''} [Category.{v''} N] [MonoidalCategory N] [BraidedCategory N]
  [RightRigidCategory N] [Preadditive N] [Linear ℂ N]
  [MonoidalPreadditive N] [MonoidalLinear ℂ N] [HasKernels N] [HasFiniteBiproducts N]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ N)]
  {ν : Type w''} [Fintype ν] (U : FiniteSemisimpleSkeleton N ν)
  (H : Sphericalized C ⥤ N) [H.Braided] [H.Additive] [H.Linear ℂ] [H.Full] [H.Faithful]

include S U in
/-- The actual negative object cannot be transparent in the preliminary
centralizer: otherwise the genuine double centralizer would put it in the
prescribed lift's essential image. -/
theorem negativeCentralObject_not_transparent (JN : PivotalStructure N)
    (hN : IsNondegenerate (C := N)) :
    negativeCentralObject T JB hJB F H ∉
      mugerCenter (C := CentralizerCategory (preliminaryAmbientObjects T JB hJB F H)) := by
  intro hz
  let G := Sphericalized.embedding T JB hJB F
  have hc : H.obj (Sphericalized.negativeGenerator (C := C)) ∈
      centralizer (centralizer (Set.range (G ⋙ H).obj)) := by
    intro Y hY
    have hy : Y ∈ centralizer (preliminaryAmbientObjects T JB hJB F H) := by
      rw [preliminaryAmbientObjects_eq_range]
      exact hY
    exact (hz ⟨Y, hy⟩ (Set.mem_univ _)).map
      (centralizerInclusion (preliminaryAmbientObjects T JB hJB F H))
  have hd := U.double_centralizer_eq JN hN (G ⋙ H).essImage
  rw [RelativeTensor.centralizer_essImage] at hd
  have hi : (G ⋙ H).essImage (H.obj (Sphericalized.negativeGenerator (C := C))) := hd ▸ hc
  obtain ⟨X, ⟨u⟩⟩ := hi
  exact Sphericalized.negativeGenerator_not_mem_lift_image S F G (Iso.refl F)
    ⟨X, ⟨H.preimageIso u⟩⟩

include S U in
/-- Epsilon's actual monodromy character is nontrivial. -/
theorem negativeCentral_monodromy_nontrivial (JN : PivotalStructure N)
    (hN : IsNondegenerate (C := N)) :
    (negativeCentralTensorInverse T JB hJB F H).monodromyCharacter ≠
      Iso.refl (𝟭 (CentralizerCategory (preliminaryAmbientObjects T JB hJB F H))) := by
  intro h
  exact negativeCentralObject_not_transparent S T JB hJB F U H JN hN
    ((negativeCentralTensorInverse T JB hJB F H).monodromyCharacter_eq_refl_iff.mp h)

/-- The actual even part has twice the original centralizer dimension.
Both factors are computed using actual tensor functors and equivalences. -/
theorem negativeCentralizer_evenFPdim_eq_twice (JN : PivotalStructure N)
    (hN : IsNondegenerate (C := N))
    (hminimal : U.fusionBasis.totalFPdim =
      2 * (Sphericalized.skeleton S).fusionBasis.totalFPdim) :
    letI := U.fullSubcategoryHasKernels
      (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
    letI := U.fullSubcategoryRightRigid
      (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
    letI := U.fullSubcategorySimpleUnit
      (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
    (U.centralizerSkeleton (preliminaryAmbientObjects T JB hJB F H)).centralizerFPdim
      {negativeCentralObject T JB hJB F H} = 2 * S.centralizerFPdim (Set.range F.obj) := by
  letI := U.fullSubcategoryHasKernels
    (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
  letI := U.fullSubcategoryRightRigid
    (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
  letI := U.fullSubcategorySimpleUnit
    (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
  exact (minimalCentralizer_evenFPdim (Sphericalized.skeleton S) U H
    (prescribedSourceObjects T JB hJB F) (negativeGenerator_mem_mugerCenter (C := C))
    JN hN hminimal Sphericalized.negativeGeneratorTensorInverse
    (Sphericalized.negativeGenerator_not_iso_unit S)).trans
      (Sphericalized.centralizerFPdim_eq_twice S F
        (Sphericalized.embedding T JB hJB F) (Iso.refl F))

/-- Formula (3.3), intrinsically in the actual preliminary fusion category. -/
theorem negativeCentralizer_totalFPdim_eq_four (JN : PivotalStructure N)
    (hN : IsNondegenerate (C := N))
    (hminimal : U.fusionBasis.totalFPdim =
      2 * (Sphericalized.skeleton S).fusionBasis.totalFPdim) :
    letI := U.fullSubcategoryHasKernels
      (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
    letI := U.fullSubcategoryRightRigid
      (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
    letI := U.fullSubcategorySimpleUnit
      (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
    (U.centralizerSkeleton (preliminaryAmbientObjects T JB hJB F H)).fusionBasis.totalFPdim =
      4 * S.centralizerFPdim (Set.range F.obj) := by
  letI := U.fullSubcategoryHasKernels
    (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
  letI := U.fullSubcategoryRightRigid
    (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
  letI := U.fullSubcategorySimpleUnit
    (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
  have hd := monodromy_indexTwo
    (U.centralizerSkeleton (preliminaryAmbientObjects T JB hJB F H))
    (negativeCentralTensorInverse T JB hJB F H) (negativeCentralSquareIso T JB hJB F H)
    (negativeCentralObject_not_transparent S T JB hJB F U H JN hN)
  rw [negativeCentralizer_evenFPdim_eq_twice S T JB hJB F U H JN hN hminimal] at hd
  linarith

/-- Formula (3.3), expressed as the actual ambient centralizer support. -/
theorem negativeCentralizerFPdim_eq_four (JN : PivotalStructure N)
    (hN : IsNondegenerate (C := N))
    (hminimal : U.fusionBasis.totalFPdim =
      2 * (Sphericalized.skeleton S).fusionBasis.totalFPdim) :
    U.centralizerFPdim (preliminaryAmbientObjects T JB hJB F H) =
      4 * S.centralizerFPdim (Set.range F.obj) := by
  letI := U.fullSubcategoryHasKernels
    (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
  letI := U.fullSubcategoryRightRigid
    (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
  letI := U.fullSubcategorySimpleUnit
    (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
  calc
    _ = (U.centralizerSkeleton (preliminaryAmbientObjects T JB hJB F H)).fusionBasis.totalFPdim :=
      (U.fullSubcategory_totalFPdim_eq
        (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))).symm
    _ = _ := negativeCentralizer_totalFPdim_eq_four S T JB hJB F U H JN hN hminimal

end Paper18.Category.PreliminaryCentralizer
