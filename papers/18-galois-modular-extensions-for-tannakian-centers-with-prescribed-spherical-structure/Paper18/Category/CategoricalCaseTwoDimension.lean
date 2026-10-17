import Paper18.Category.CategoricalCaseTwoDimensionCenter
import Paper18.Category.DiagonalCondensationIntersectionCommonPartDimension
import Paper18.Category.DeligneProductNondegenerate

/-! # The actual Case 2 local centralizer product dimension

The diagonal object is specified by its actual simple-pair isomorphism.
Its local centralizer dimension and its image intersection are then
computed by the constructed categorical condensation and mixed-Hom APIs.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators MonObj
universe vN uN wN vB uB wB vP uP wP
namespace Paper18.Category.CategoricalCaseTwo
open DiagonalCondensation
attribute [local instance 2000] RightRigidCategory.rightDual
variable {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [HasKernels N] [HasFiniteBiproducts N] [RightRigidCategory N] [Simple (𝟙_ N)]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [Linear ℂ B]
  [MonoidalCategory B] [BraidedCategory B] [MonoidalPreadditive B] [MonoidalLinear ℂ B]
  [HasKernels B] [HasFiniteBiproducts B] [RightRigidCategory B] [Simple (𝟙_ B)]
  [∀ X Y : B, FiniteDimensional ℂ (X ⟶ Y)]
  {P : Type uP} [Category.{vP} P] [Preadditive P] [Linear ℂ P]
  [MonoidalCategory P] [BraidedCategory P] [MonoidalPreadditive P] [MonoidalLinear ℂ P]
  [HasKernels P] [HasFiniteBiproducts P] [RightRigidCategory P] [Simple (𝟙_ P)]
  [∀ X Y : P, FiniteDimensional ℂ (X ⟶ Y)]
  {ιN : Type wN} [Fintype ιN] (SN : FiniteSemisimpleSkeleton N ιN)
  {ιB : Type wB} [Fintype ιB] (SB : FiniteSemisimpleSkeleton B ιB)
  {ιP : Type wP} [Fintype ιP] (SP : FiniteSemisimpleSkeleton P ιP)
  (H : B ⥤ N) [H.Additive] [H.Linear ℂ] [H.Braided] [H.Full] [H.Faithful]
  (χ : 𝟭 (CentralizerCategory (Set.range H.obj)) ≅ 𝟭 (CentralizerCategory (Set.range H.obj)))
  [NatTrans.IsMonoidal χ.hom]
  (G : SignKernel.Positive χ ⥤ P) [G.Additive] [G.Monoidal] [G.Linear ℂ] [G.Full] [G.Faithful]
  [HasKernels (DeligneProduct N P)] [Simple (𝟙_ (DeligneProduct N P))]
  [HasCoequalizers (DeligneProduct N P)]

include SB in
set_option maxHeartbeats 1000000 in
/-- The Case 2 actual local centralizer and actual image intersection have
exactly the product dimension of the original transparent center and the
actual second centralizer. All four dimension identities and the actual
intersection identification are proved categorical theorems. -/
theorem local_product_dimension
    (JN : PivotalStructure N) (hN : IsNondegenerate (C := N))
    (JP : PivotalStructure P) (hP : IsNondegenerate (C := P))
    (hχ : ∀ X, χ.hom.app X ≫ χ.hom.app X = 𝟙 X)
    (X : CentralizerCategory (Set.range H.obj))
    (hZ : X ∈ mugerCenter) (hX : χ.hom.app X ≠ 𝟙 X)
    (hG : ∀ X Y, Centralizes X Y → Centralizes (G.obj X) (G.obj Y)) :
    letI := SN.fullSubcategoryHasKernels (centralizerProperty (Set.range H.obj))
    letI := SN.fullSubcategoryRightRigid (centralizerProperty (Set.range H.obj))
    letI := SN.fullSubcategorySimpleUnit (centralizerProperty (Set.range H.obj))
    let SK := SN.centralizerSkeleton (Set.range H.obj)
    letI := SignKernel.hasKernels χ SK
    letI := SignKernel.rightRigid χ SK
    letI := SignKernel.simpleUnit χ SK
    let SKP := SignKernel.skeleton χ SK
    let F := positiveAmbientInclusion H χ
    ∀ {A : DeligneProduct N P} [MonObj A] [IsCommMonObj A]
      (e : A ≅ ⨁ fun i => pair (F.obj (SKP.simpleObject i))
        (G.obj (dual (SignKernel.Positive χ) (SKP.simpleObject i))))
      (R : SeparableAlgebra A) (Ψ : ModuleBalancing.MultiplicationPairing A)
      (JW : PivotalStructure (DeligneProduct N P))
      (hA : (JW.twistIso A).hom = 𝟙 A)
      (hconnected : Module.finrank ℂ (𝟙_ (DeligneProduct N P) ⟶ A) = 1),
    let SW := DeligneProduct.skeleton SN SP
    letI := R.localHasKernels SW
    letI := R.localRightRigid SW hconnected
    letI := R.localSimpleUnit SW hconnected
    let SM := R.localSkeleton SW
    let hB := fun (Y : B) i => positive_centralizes_original H χ (SKP.simpleObject i) Y
    let hE := fun (Y : (ambientCenterProperty H).FullSubcategory) i =>
      positive_centralizes_ambient_center H χ (SKP.simpleObject i) Y
    let HB := leftLocalFunctor (fun i => F.obj (SKP.simpleObject i))
      (fun i => G.obj (dual (SignKernel.Positive χ) (SKP.simpleObject i))) e H hB
    let FE := restrictedLeftLocal SKP F G e (ambientCenterProperty H) hE
    let GI := restrictedRightLocal SKP F G e (secondCentralizer G)
      (secondCentralizer_local_condition SKP G)
    SM.centralizerFPdim (Set.range HB.obj) *
      SM.supportFPdim (fun M => FE.essImage M ∧ GI.essImage M) =
        SN.supportFPdim (ambientCenterProperty H) * SP.centralizerFPdim (Set.range G.obj) := by
  letI := SN.fullSubcategoryHasKernels (centralizerProperty (Set.range H.obj))
  letI := SN.fullSubcategoryRightRigid (centralizerProperty (Set.range H.obj))
  letI := SN.fullSubcategorySimpleUnit (centralizerProperty (Set.range H.obj))
  let SK := SN.centralizerSkeleton (Set.range H.obj)
  letI := SignKernel.hasKernels χ SK
  letI := SignKernel.rightRigid χ SK
  letI := SignKernel.simpleUnit χ SK
  let SKP := SignKernel.skeleton χ SK
  let F := positiveAmbientInclusion H χ
  dsimp only
  intro A instA instAc e R Ψ JW hA hconnected
  let SW := DeligneProduct.skeleton SN SP
  letI := R.localHasKernels SW
  letI := R.localRightRigid SW hconnected
  letI := R.localSimpleUnit SW hconnected
  let SM := R.localSkeleton SW
  let hB := fun (Y : B) i => positive_centralizes_original H χ (SKP.simpleObject i) Y
  let hE := fun (Y : (ambientCenterProperty H).FullSubcategory) i =>
    positive_centralizes_ambient_center H χ (SKP.simpleObject i) Y
  let HB := leftLocalFunctor (fun i => F.obj (SKP.simpleObject i))
    (fun i => G.obj (dual (SignKernel.Positive χ) (SKP.simpleObject i))) e H hB
  let FE := restrictedLeftLocal SKP F G e (ambientCenterProperty H) hE
  let GI := restrictedRightLocal SKP F G e (secondCentralizer G)
    (secondCentralizer_local_condition SKP G)
  change SM.centralizerFPdim (Set.range HB.obj) *
    SM.supportFPdim (fun M => FE.essImage M ∧ GI.essImage M) =
      SN.supportFPdim (ambientCenterProperty H) * SP.centralizerFPdim (Set.range G.obj)
  have hinter := commonPart_supportFPdim_intersection SKP F G SN SP e (R.skeleton SW)
    (ambientCenterProperty H) hE hG SM
  rw [hinter, positive_commonPartFPdim H χ SN hχ X hZ hX]
  have hW := DeligneProduct.isNondegenerate SN SP hN hP
  have hd := leftLocalCentralizerFPdim SN SP SKP F G e R SB H hB Ψ JW hA hconnected hW
  change SM.centralizerFPdim (Set.range HB.obj) = _ at hd
  rw [hd, ← ambientCenterFPdim H SN]
  exact centralizer_quotient_product SN SB SP H χ G JN hN JP hP hχ X hZ hX

end Paper18.Category.CategoricalCaseTwo
