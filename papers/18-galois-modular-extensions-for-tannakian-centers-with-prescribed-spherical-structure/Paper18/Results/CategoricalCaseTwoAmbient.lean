import Paper18.Results.CategoricalCaseTwoCondensationEmbedding
import Paper18.Results.CategoricalCaseTwoPivotal
import Paper18.Results.CategoricalCentralizerTannakian
import Paper18.Category.CategoricalCaseTwoDimensionIntegral
import Paper18.Category.PositiveMonoidalFunctor
import Paper18.Category.TannakianIntegral

/-! # The actual Case 2 modular extension

The shared category is the actual positive sign kernel of the actual
ambient centralizer. The canonical diagonal algebra constructs the local
modular category. Its integral centralizer follows from the actual join,
intersection and index-two dimension theorems.
-/
noncomputable section
set_option maxHeartbeats 4000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe vN uN wN vB uB wB vP uP wP
namespace Paper18.Category.CaseTwoCondensation
attribute [local instance 2000] RightRigidCategory.rightDual
variable {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [bN : BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [HasKernels N] [HasFiniteBiproducts N] [RightRigidCategory N] [Simple (𝟙_ N)]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [Linear ℂ B]
  [MonoidalCategory B] [BraidedCategory B] [MonoidalPreadditive B] [MonoidalLinear ℂ B]
  [HasKernels B] [HasFiniteBiproducts B] [RightRigidCategory B] [Simple (𝟙_ B)]
  [∀ X Y : B, FiniteDimensional ℂ (X ⟶ Y)]
  {P : Type uP} [Category.{vP} P] [Preadditive P] [Linear ℂ P]
  [MonoidalCategory P] [bP : BraidedCategory P] [MonoidalPreadditive P] [MonoidalLinear ℂ P]
  [HasKernels P] [HasFiniteBiproducts P] [RightRigidCategory P] [Simple (𝟙_ P)]
  [∀ X Y : P, FiniteDimensional ℂ (X ⟶ Y)]
  {ιN : Type wN} [Fintype ιN] (SN : FiniteSemisimpleSkeleton N ιN)
  {ιB : Type wB} [Fintype ιB] (SB : FiniteSemisimpleSkeleton B ιB)
  {ιP : Type wP} [Fintype ιP] (SP : FiniteSemisimpleSkeleton P ιP)
  (JB : PivotalStructure B) (JN : PivotalStructure N) (JP : PivotalStructure P)
  (H : BraidedSphericalEmbedding JB JN)
  {Γ : Type} [Group Γ] (TB : TannakianCenter B Γ)

/-- The actual Case 2 construction, given an actual positive modular
extension of the sign kernel with integral centralizer. The original
ambient centralizer's weak integrality is the genuine preliminary
intermediate conclusion. No local algebra, local modularity, free
embedding or final centralizer-integrality premise is received. -/
def modularExtension (hN : IsModular JN) (hJP : JP.Positive)
    (hP : IsNondegenerate (C := P)) :
    letI := SN.fullSubcategoryHasKernels (centralizerProperty (Set.range H.functor.obj))
    letI := SN.fullSubcategoryRightRigid (centralizerProperty (Set.range H.functor.obj))
    letI := SN.fullSubcategorySimpleUnit (centralizerProperty (Set.range H.functor.obj))
    let SK := SN.centralizerSkeleton (Set.range H.functor.obj)
    let JK := SN.centralizerPivotal (Set.range H.functor.obj) JN
    let hJK := SN.fullSubcategoryPivotal_spherical
      (centralizerProperty (Set.range H.functor.obj)) JN hN.1
    ∀ (hweak : SK.fusionBasis.WeaklyIntegral),
    let Kpos := JK.canonicalPositive SK hJK hweak
    let χ := JK.ratio Kpos
    ∀ (X : CentralizerCategory (Set.range H.functor.obj))
      (hZ : X ∈ mugerCenter) (hX : χ.hom.app X ≠ 𝟙 X),
    letI := SignKernel.hasKernels χ SK
    letI := SignKernel.rightRigid χ SK
    letI := SignKernel.simpleUnit χ SK
    ∀ (G : SignKernel.Positive χ ⥤ P) [G.Additive] [G.Linear ℂ] [G.Braided]
      [G.Full] [G.Faithful]
      (hII : SP.CentralizerIntegral (Set.range G.obj)),
    ModularExtension JB := by
  letI := SN.fullSubcategoryHasKernels (centralizerProperty (Set.range H.functor.obj))
  letI := SN.fullSubcategoryRightRigid (centralizerProperty (Set.range H.functor.obj))
  letI := SN.fullSubcategorySimpleUnit (centralizerProperty (Set.range H.functor.obj))
  let SK := SN.centralizerSkeleton (Set.range H.functor.obj)
  let JK := SN.centralizerPivotal (Set.range H.functor.obj) JN
  let hJK := SN.fullSubcategoryPivotal_spherical
    (centralizerProperty (Set.range H.functor.obj)) JN hN.1
  dsimp only
  intro hweak
  let Kpos := JK.canonicalPositive SK hJK hweak
  let χ := JK.ratio Kpos
  intro X hZ hX
  letI := SignKernel.hasKernels χ SK
  letI := SignKernel.rightRigid χ SK
  letI := SignKernel.simpleUnit χ SK
  intro G instGa instGl instGb instGf instGfaith hII
  let SE := SignKernel.skeleton χ SK
  let JE := SignKernel.pivotal χ SK JK
  have hJE : JE.Spherical := SignKernel.pivotal_spherical χ SK JK hJK
  have pJE : JE.Positive := ratio_positive_kernel_positive SK JK Kpos
    (JK.canonicalPositive_positive SK hJK hweak)
  let F : BraidedSphericalEmbedding JE JN :=
    { functor := CategoricalCaseTwo.positiveAmbientInclusion H.functor χ
      pivotal := (SignKernel.inclusion_preservesPivotal χ SK JK).comp
        (SN.fullSubcategory_preservesPivotal
          (centralizerProperty (Set.range H.functor.obj)) JN) }
  let GG : BraidedSphericalEmbedding JE JP :=
    { functor := G
      pivotal := preservesPivotal_of_positive_fullyFaithful G JE JP SE SP pJE hJP }
  let hH := fun (Y : B) i =>
    CategoricalCaseTwo.positive_centralizes_original H.functor χ (SE.simpleObject i) Y
  letI := DeligneProduct.hasKernels SN SP
  letI := DeligneProduct.simpleUnit SN SP
  let SW := DeligneProduct.skeleton SN SP
  letI := SW.hasCoequalizers
  let M := Ambient SE JE JN JP F GG
  let R := separable SE JE JN JP F GG hJE
  let Ψ := multiplicationPairing SE JE JN JP F GG
  let hconn := algebra_connected SE JE JN JP F GG
  let JW := productPivotal JN JP
  let hA := algebra_twist SE JE JN JP F GG hJE
  letI : BraidedCategory (DeligneProduct N P) := DeligneProduct.reverseSecondBraiding N P
  letI : IsCommMonObj (algebra SE JE JN JP F GG) := algebra_commutative SE JE JN JP F GG
  letI := ambientHasKernels SE SN SP JE JN JP F GG hJE
  letI := ambientRightRigid SE SN SP JE JN JP F GG hJE
  letI := ambientSimpleUnit SE SN SP JE JN JP F GG hJE
  let SM := ambientSkeleton SE SN SP JE JN JP F GG hJE
  let JM := ambientPivotal SE SN SP JE JN JP F GG hJE
  let HB := ambientEmbedding SE SN SP JE JN JP F GG JB H hH hJE
  have hM := ambient_modular SE SN SP JE JN JP F GG hJE hN
    ⟨JP.spherical_of_positive SP hJP, hP⟩
  have hEI : SN.FullSubcategoryIntegral (CategoricalCaseTwo.ambientCenterProperty H.functor) := by
    let TC := TB.centralizerCenter H.functor SN JN hN.2
    letI := TC.finite_group
    letI := Fintype.ofFinite Γ
    exact CategoricalCaseTwo.ambientCenter_integral H.functor SN (TC.center_integral SK)
  have hχ (Y) : χ.hom.app Y ≫ χ.hom.app Y = 𝟙 Y :=
    comparison_involutive SK JK Kpos hJK (JK.canonicalPositive_spherical SK hJK hweak) Y
  have hG (Y Z : SignKernel.Positive χ) (h : Centralizes Y Z) :
      @Centralizes P _ _ (@reverseBraiding P _ _ bP) (G.obj Y) (G.obj Z) :=
    (RelativeTensor.centralizes_reverse_iff _ _).mpr (h.map G)
  have hPr := (RelativeTensor.nondegenerate_reverse_iff (C := P)).mpr hP
  have hII0 := (SP.centralizerIntegral_iff (Set.range G.obj)).mp hII
  have hcrev (Y Z : P) :
      @Centralizes P _ _ (@reverseBraiding P _ _ bP) Y Z ↔ Centralizes Y Z :=
    RelativeTensor.centralizes_reverse_iff Y Z
  have hIIr :
      letI : BraidedCategory P := reverseBraiding P
      SP.CentralizerIntegral (Set.range G.obj) := by
    letI : BraidedCategory P := reverseBraiding P
    apply (SP.centralizerIntegral_iff _).mpr
    intro i hi
    apply hII0 i
    intro Y hY
    exact (hcrev _ _).mp (hi Y hY)
  have hD : SM.CentralizerIntegral (Set.range HB.functor.obj) := by
    have e := DiagonalAlgebra.productCanonicalAlgebraIso SE F.functor G
    let GF := G
    letI : BraidedCategory P := reverseBraiding P
    have hd := CategoricalCaseTwo.localCentralizer_eq_join_and_integral
      SN SB SP H.functor χ GF JN hN.2 JP hPr hχ X hZ hX hG e R Ψ JW hA hconn hEI hIIr
    exact hd.2
  exact
    { ambient := M
      index := AmbientIndex SE SN SP JE JN JP F GG hJE
      skeleton := SM
      pivotal := JM
      modular := hM
      embedding := HB
      integralCentralizer := hD }

end Paper18.Category.CaseTwoCondensation
