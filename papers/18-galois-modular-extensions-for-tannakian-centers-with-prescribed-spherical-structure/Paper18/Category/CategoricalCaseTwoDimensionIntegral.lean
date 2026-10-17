import Paper18.Category.CategoricalCaseTwoDimension
import Paper18.Category.CategoricalCaseTwoDimensionCenterIntegral
import Paper18.Category.DiagonalCondensationIntersectionIntegral

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
set_option maxHeartbeats 1500000 in
/-- The actual Case 2 centralizer is exactly the join of its two actual
integral local free images, and is integral. The full local condensation,
shared-image identification and character index-two calculation supply
its dimension; no product-dimension hypothesis is accepted. -/
theorem localCentralizer_eq_join_and_integral
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
    ∀ (hEI : SN.FullSubcategoryIntegral (ambientCenterProperty H))
      (hII : SP.CentralizerIntegral (Set.range G.obj)),
    fusionJoin FE.essImage GI.essImage = centralizerProperty (Set.range HB.obj) ∧
      SM.FullSubcategoryIntegral (centralizerProperty (Set.range HB.obj)) := by
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
  intro A instA instAc e R Ψ JW hA hconnected hEI hII
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

  letI := SN.fullSubcategoryHasKernels (ambientCenterProperty H)
  letI := SN.fullSubcategoryRightRigid (ambientCenterProperty H)
  letI := SN.fullSubcategorySimpleUnit (ambientCenterProperty H)
  let TE := SN.fullSubcategorySkeleton (ambientCenterProperty H)
  letI := SP.fullSubcategoryHasKernels (secondCentralizer G)
  letI := SP.fullSubcategoryRightRigid (secondCentralizer G)
  letI := SP.fullSubcategorySimpleUnit (secondCentralizer G)
  let TI := SP.centralizerSkeleton (Set.range G.obj)
  let ffE := restrictedLeftLocalFullyFaithful SKP F G SN e (ambientCenterProperty H) hE
  letI := ffE.full
  letI := ffE.faithful
  let ffI := restrictedRightLocalFullyFaithful SKP F G SP e (secondCentralizer G)
    (secondCentralizer_local_condition SKP G)
  letI := ffI.full
  letI := ffI.faithful
  change fusionJoin FE.essImage GI.essImage = centralizerProperty (Set.range HB.obj) ∧
    SM.FullSubcategoryIntegral (centralizerProperty (Set.range HB.obj))
  have hd0 := local_product_dimension SN SB SP H χ G JN hN JP hP hχ X hZ hX hG e R Ψ JW hA hconnected
  change SM.centralizerFPdim (Set.range HB.obj) *
    SM.supportFPdim (fun M => FE.essImage M ∧ GI.essImage M) =
      SN.supportFPdim (ambientCenterProperty H) * SP.centralizerFPdim (Set.range G.obj) at hd0
  have hd : SM.centralizerFPdim (Set.range HB.obj) *
      SM.supportFPdim (fun M => FE.essImage M ∧ GI.essImage M) =
        TE.fusionBasis.totalFPdim * TI.fusionBasis.totalFPdim := by
    rw [SN.fullSubcategory_totalFPdim_eq (ambientCenterProperty H),
      ← SP.centralizerFPdim_eq_intrinsic (Set.range G.obj)]
    exact hd0
  have hcrossE (Y : (ambientCenterProperty H).FullSubcategory) (Z : B) :
      Centralizes (FE.obj Y) (HB.obj Z) := by
    let L : N ⥤ DeligneProduct N P := DeligneProduct.left
    exact localFreeAlong_centralizes ((ambientCenterProperty H).ι ⋙ L)
      (fun Y => centralizes_diagonal_left _ _ e Y.obj (hE Y)) (H ⋙ L)
      (fun Z => centralizes_diagonal_left _ _ e (H.obj Z) (hB Z)) Y Z
      ((Y.property.1 (H.obj Z) ⟨Z,rfl⟩).map L)
  have hcrossI (Y : (secondCentralizer G).FullSubcategory) (Z : B) :
      Centralizes (GI.obj Y) (HB.obj Z) := by
    exact (local_left_right_centralizes _ _ e H hB (secondCentralizer G).ι
      (secondCentralizer_local_condition SKP G) Z Y).symm
  have hW := DeligneProduct.isNondegenerate SN SP hN hP
  have hM := R.localNondegenerate SW Ψ JW hA hconnected hW
  exact imageCentralizer_eq_join_and_integral SM (ModuleBalancing.localPivotal JW hA) hM
    TE TI FE GI HB hcrossE hcrossI hd hEI hII

end Paper18.Category.CategoricalCaseTwo
