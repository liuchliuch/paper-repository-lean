import Paper18.Results.CategoricalCaseOneExtension
import Paper18.Results.CategoricalCaseTwoAmbient
import Paper18.Category.PositiveGaloisExtensionRefinement
import Paper18.Category.TannakianSignKernel
import Paper18.External.JohnsonFreyd23

/-! # The actual two sign-character branches of Theorem 1.1

Only Johnson--Freyd's nonspherical extension theorem is an external input.
The positive extension of the genuine sign kernel, all case constructions,
and their actual spherical embeddings are derived internally. The two
universe presentations of the output are kept explicit here.
-/
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe vB uB wB vN uN wN vP uP wP
namespace Paper18.Category.CategoricalTheorem11
attribute [local instance 2000] RightRigidCategory.rightDual
variable {B : Type uB} [Category.{vB} B] [Preadditive B] [Linear ℂ B]
  [MonoidalCategory B] [BraidedCategory B] [MonoidalPreadditive B] [MonoidalLinear ℂ B]
  [HasKernels B] [HasFiniteBiproducts B] [RightRigidCategory B] [Simple (𝟙_ B)]
  [∀ X Y : B, FiniteDimensional ℂ (X ⟶ Y)]
  {ιB : Type wB} [Fintype ιB] (SB : FiniteSemisimpleSkeleton B ιB)
  (JB : PivotalStructure B)
  {Γ : Type} [Group Γ] (TB : TannakianCenter B Γ)
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [HasKernels N] [HasFiniteBiproducts N] [RightRigidCategory N] [Simple (𝟙_ N)]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  {ιN : Type wN} [Fintype ιN] (SN : FiniteSemisimpleSkeleton N ιN)
  (JN : PivotalStructure N) (H : BraidedSphericalEmbedding JB JN)

/-- The integral even centralizer supplies the actual weak integrality
and positive pivotal structure. The restriction of the actual comparison
character then selects one of the two proved actual constructions. -/
def fromAmbientCasesAt (jf : Paper18.External.JohnsonFreyd23At.{vN,uN,wN,vP,uP,wP})
    (hN : IsModular JN) :
    letI := SN.fullSubcategoryHasKernels (centralizerProperty (Set.range H.functor.obj))
    letI := SN.fullSubcategoryRightRigid (centralizerProperty (Set.range H.functor.obj))
    letI := SN.fullSubcategorySimpleUnit (centralizerProperty (Set.range H.functor.obj))
    ∀ (e : CentralizerCategory (Set.range H.functor.obj)) (E : TensorInverse e)
      (he : e ⊗ e ≅ 𝟙_ (CentralizerCategory (Set.range H.functor.obj)))
      (hI : (SN.centralizerSkeleton (Set.range H.functor.obj)).CentralizerIntegral {e})
      (hd : (SN.centralizerPivotal (Set.range H.functor.obj) JN).rightDim e = -1),
    Nonempty (ModularExtension.{vB,uB,vN,uN,wN} JB) ∨
      Nonempty (ModularExtension.{vB,uB,max vN vP,max 1 (max (max uN uP) (max vN vP)),max wN wP} JB) := by
  letI := SN.fullSubcategoryHasKernels (centralizerProperty (Set.range H.functor.obj))
  letI := SN.fullSubcategoryRightRigid (centralizerProperty (Set.range H.functor.obj))
  letI := SN.fullSubcategorySimpleUnit (centralizerProperty (Set.range H.functor.obj))
  intro e E he hI hd
  let SK := SN.centralizerSkeleton (Set.range H.functor.obj)
  let JK := SN.centralizerPivotal (Set.range H.functor.obj) JN
  let hJK := SN.fullSubcategoryPivotal_spherical
    (centralizerProperty (Set.range H.functor.obj)) JN hN.1
  let hweak := SK.weaklyIntegral_of_orderTwo_centralizerIntegral E he hI
  let Kpos := JK.canonicalPositive SK hJK hweak
  let χ := JK.ratio Kpos
  by_cases hcenter : ∀ X ∈ mugerCenter (C := CentralizerCategory (Set.range H.functor.obj)),
      χ.hom.app X = 𝟙 X
  · exact Or.inl ⟨caseOneModularExtension SN TB JB JN H hN E he hI hcenter hd⟩
  · push_neg at hcenter
    obtain ⟨X, hZ, hX⟩ := hcenter
    let TK := TB.centralizerCenter H.functor SN JN hN.2
    letI := TK.finite_group
    letI := Fintype.ofFinite Γ
    have hχ (Y) : χ.hom.app Y ≫ χ.hom.app Y = 𝟙 Y :=
      comparison_involutive SK JK Kpos hJK (JK.canonicalPositive_spherical SK hJK hweak) Y
    letI := SignKernel.hasKernels χ SK
    letI := SignKernel.rightRigid χ SK
    letI := SignKernel.simpleUnit χ SK
    let SE := SignKernel.skeleton χ SK
    let JE := SignKernel.pivotal χ SK JK
    let TE := TannakianSignKernel.positiveTannakianCenter TK χ SK hχ X hZ hX
    have hJE : JE.Positive := ratio_positive_kernel_positive SK JK Kpos
      (JK.canonicalPositive_positive SK hJK hweak)
    obtain ⟨E0⟩ := jf SE TE
    obtain ⟨P⟩ := E0.exists_positiveRefinement SE JE hJE
    exact Or.inr ⟨CaseTwoCondensation.modularExtension SN SB P.skeleton JB JN P.pivotal
      H TB hN P.positive P.nondegenerate hweak X hZ hX P.inclusion P.integralCentralizer⟩

end Paper18.Category.CategoricalTheorem11
