import Paper18.Results.CategoricalPreliminaryCentralizerSphericalized

/-! # The preliminary category used in the proof of the main theorem -/
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

/-- The actual preliminary fusion category is spherical and weakly
integral, with its actual negative object and integral even centralizer.
The original ambient category has no pivotal-structure premise. -/
theorem sphericalized_preliminary (JN : PivotalStructure N) (hJN : JN.Spherical)
    (hp : PreservesPivotal H (Sphericalized.pivotalStructure (C := C)) JN)
    (hN : IsNondegenerate (C := N))
    (hminimal : U.fusionBasis.totalFPdim =
      2 * (Sphericalized.skeleton S).fusionBasis.totalFPdim)
    (hI : S.CentralizerIntegral (Set.range F.obj)) :
    letI := U.fullSubcategoryHasKernels
      (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
    letI := U.fullSubcategoryRightRigid
      (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
    letI := U.fullSubcategorySimpleUnit
      (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
    (U.centralizerPivotal (preliminaryAmbientObjects T JB hJB F H) JN).Spherical ∧
      (U.centralizerPivotal (preliminaryAmbientObjects T JB hJB F H) JN).rightDim
        (negativeCentralObject T JB hJB F H) = -1 ∧
      (U.centralizerSkeleton (preliminaryAmbientObjects T JB hJB F H)).CentralizerIntegral
        {negativeCentralObject T JB hJB F H} ∧
      (U.centralizerSkeleton (preliminaryAmbientObjects T JB hJB F H)).fusionBasis.WeaklyIntegral := by
  letI := U.fullSubcategoryHasKernels
    (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
  letI := U.fullSubcategoryRightRigid
    (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
  letI := U.fullSubcategorySimpleUnit
    (centralizerProperty (preliminaryAmbientObjects T JB hJB F H))
  exact ⟨U.fullSubcategoryPivotal_spherical
      (centralizerProperty (preliminaryAmbientObjects T JB hJB F H)) JN hJN,
    negativeCentralObject_rightDim S T JB hJB F U H JN hp,
    negativeCentralizer_evenIntegral S T JB hJB F U H JN hN hminimal hI,
    negativeCentralizer_weaklyIntegral S T JB hJB F U H JN hN hminimal hI⟩

end Paper18.Category.PreliminaryCentralizer
