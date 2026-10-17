import Paper18.Results.CategoricalCaseOneAmbient
import Paper18.Category.ModularExtensionOfEmbedding

/-! # The actual modular extension produced in the first case -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u v' u' w'
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [Simple (𝟙_ C)]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [BraidedCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D] [RightRigidCategory D] [Simple (𝟙_ D)]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w'} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  {G : Type} [Group G] (T : TannakianCenter C G)
  (JB : PivotalStructure C) (JN : PivotalStructure D)
  (H : BraidedSphericalEmbedding JB JN)

/-- Case 1 constructs the paper's actual modular-extension output. The
actual weak-integrality and positive-structure inputs are derived internally
from the actual integral even centralizer. -/
def caseOneModularExtension (hN : IsModular JN) :
    letI := S.fullSubcategoryHasKernels (centralizerProperty (Set.range H.functor.obj))
    letI := S.fullSubcategoryRightRigid (centralizerProperty (Set.range H.functor.obj))
    letI := S.fullSubcategorySimpleUnit (centralizerProperty (Set.range H.functor.obj))
    ∀ {e : CentralizerCategory (Set.range H.functor.obj)} (E : TensorInverse e)
      (he : e ⊗ e ≅ 𝟙_ (CentralizerCategory (Set.range H.functor.obj)))
      (hI : (S.centralizerSkeleton (Set.range H.functor.obj)).CentralizerIntegral {e}),
    let hweak := (S.centralizerSkeleton (Set.range H.functor.obj)).weaklyIntegral_of_orderTwo_centralizerIntegral E he hI
    ∀ (hcenter : ∀ X ∈ mugerCenter (C := CentralizerCategory (Set.range H.functor.obj)),
      ((S.centralizerPivotal (Set.range H.functor.obj) JN).ratio
        ((S.centralizerPivotal (Set.range H.functor.obj) JN).canonicalPositive
          (S.centralizerSkeleton (Set.range H.functor.obj))
          (S.fullSubcategoryPivotal_spherical (centralizerProperty (Set.range H.functor.obj)) JN hN.1)
          hweak)).hom.app X = 𝟙 X)
      (hd : (S.centralizerPivotal (Set.range H.functor.obj) JN).rightDim e = -1),
    ModularExtension.{v,u,v',u',w'} JB := by
  letI := S.fullSubcategoryHasKernels (centralizerProperty (Set.range H.functor.obj))
  letI := S.fullSubcategoryRightRigid (centralizerProperty (Set.range H.functor.obj))
  letI := S.fullSubcategorySimpleUnit (centralizerProperty (Set.range H.functor.obj))
  intro e E he hI hweak hcenter hd
  exact ModularExtension.ofEmbedding S hN H
    (centralizer_integral_case_one S H.functor T JN hN.1 hN.2 E he hI hcenter hd)

end Paper18.Category
