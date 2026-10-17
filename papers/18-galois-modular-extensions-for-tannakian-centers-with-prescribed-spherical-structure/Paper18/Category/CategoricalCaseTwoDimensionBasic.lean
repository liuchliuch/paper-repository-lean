import Paper18.Category.DiagonalCondensationDimension
import Paper18.Category.SignKernelCenterDimensions

/-! # The actual centralizer and sign-kernel dimensions in Case 2 -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe vN uN wN vB uB wB vP uP wP
namespace Paper18.Category.CategoricalCaseTwo
attribute [local instance 2000] RightRigidCategory.rightDual
variable {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [HasKernels N] [HasFiniteBiproducts N] [RightRigidCategory N] [Simple (𝟙_ N)]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [Linear ℂ B]
  [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalLinear ℂ B]
  [HasKernels B] [HasFiniteBiproducts B] [RightRigidCategory B] [Simple (𝟙_ B)]
  [∀ X Y : B, FiniteDimensional ℂ (X ⟶ Y)]
  {P : Type uP} [Category.{vP} P] [Preadditive P] [Linear ℂ P]
  [MonoidalCategory P] [BraidedCategory P] [MonoidalPreadditive P] [MonoidalLinear ℂ P]
  [HasKernels P] [HasFiniteBiproducts P] [RightRigidCategory P] [Simple (𝟙_ P)]
  [∀ X Y : P, FiniteDimensional ℂ (X ⟶ Y)]
  {ιN : Type wN} [Fintype ιN] (SN : FiniteSemisimpleSkeleton N ιN)
  {ιB : Type wB} [Fintype ιB] (SB : FiniteSemisimpleSkeleton B ιB)
  {ιP : Type wP} [Fintype ιP] (SP : FiniteSemisimpleSkeleton P ιP)
  (H : B ⥤ N) [H.Additive] [H.Monoidal] [H.Linear ℂ] [H.Full] [H.Faithful]
  (χ : 𝟭 (CentralizerCategory (Set.range H.obj)) ≅ 𝟭 (CentralizerCategory (Set.range H.obj)))
  [NatTrans.IsMonoidal χ.hom]
  (G : SignKernel.Positive χ ⥤ P) [G.Additive] [G.Monoidal] [G.Linear ℂ] [G.Full] [G.Faithful]

/-- The Case 2 dimension product is forced by the actual ambient
centralizer, the actual positive sign kernel and its transparent center,
and the actual second-factor centralizer. No numerical dimension law or
final product equality is an input. -/
theorem centralizer_quotient_product
    (JN : PivotalStructure N) (hN : IsNondegenerate (C := N))
    (JP : PivotalStructure P) (hP : IsNondegenerate (C := P))
    (hχ : ∀ X, χ.hom.app X ≫ χ.hom.app X = 𝟙 X)
    (X : CentralizerCategory (Set.range H.obj))
    (hZ : X ∈ mugerCenter) (hX : χ.hom.app X ≠ 𝟙 X) :
    letI := SN.fullSubcategoryHasKernels (centralizerProperty (Set.range H.obj))
    letI := SN.fullSubcategoryRightRigid (centralizerProperty (Set.range H.obj))
    letI := SN.fullSubcategorySimpleUnit (centralizerProperty (Set.range H.obj))
    let SK := SN.centralizerSkeleton (Set.range H.obj)
    (SN.fusionBasis.totalFPdim * SP.fusionBasis.totalFPdim /
      (SB.fusionBasis.totalFPdim * SignKernel.positiveTotalFPdim SK χ ^ 2)) *
        SignKernel.positiveCenterFPdim SK χ =
      SK.centralizerFPdim (Set.univ : Set (CentralizerCategory (Set.range H.obj))) *
        SP.centralizerFPdim (Set.range G.obj) := by
  letI := SN.fullSubcategoryHasKernels (centralizerProperty (Set.range H.obj))
  letI := SN.fullSubcategoryRightRigid (centralizerProperty (Set.range H.obj))
  letI := SN.fullSubcategorySimpleUnit (centralizerProperty (Set.range H.obj))
  let SK := SN.centralizerSkeleton (Set.range H.obj)
  letI := SignKernel.hasKernels χ SK
  letI := SignKernel.rightRigid χ SK
  letI := SignKernel.simpleUnit χ SK
  let SKP := SignKernel.skeleton χ SK
  change (SN.fusionBasis.totalFPdim * SP.fusionBasis.totalFPdim /
    (SB.fusionBasis.totalFPdim * SignKernel.positiveTotalFPdim SK χ ^ 2)) *
      SignKernel.positiveCenterFPdim SK χ =
    SK.centralizerFPdim (Set.univ : Set (CentralizerCategory (Set.range H.obj))) *
      SP.centralizerFPdim (Set.range G.obj)
  have hk : SK.fusionBasis.totalFPdim = SN.fusionBasis.totalFPdim / SB.fusionBasis.totalFPdim := by
    calc
      _ = SN.centralizerFPdim (Set.range H.obj) := (SN.centralizerFPdim_eq_intrinsic _).symm
      _ = _ := DiagonalCondensation.centralizerFPdim_of_fullyFaithful SB SN H JN hN
  have hi : SP.centralizerFPdim (Set.range G.obj) =
      SP.fusionBasis.totalFPdim / SignKernel.positiveTotalFPdim SK χ := by
    exact DiagonalCondensation.centralizerFPdim_of_fullyFaithful SKP SP G JP hP
  have htwo := SignKernel.total_and_center_indexTwo SK χ hχ X hZ hX
  have hb : SB.fusionBasis.totalFPdim ≠ 0 := by
    apply ne_of_gt
    exact Finset.sum_pos' (fun i _ => sq_nonneg (SB.fusionBasis.fpdim i))
      ⟨SB.fusionBasis.one, Finset.mem_univ _, pow_pos (SB.fusionBasis.fpdim_pos _) _⟩
  have hq : SignKernel.positiveTotalFPdim SK χ ≠ 0 := by
    apply ne_of_gt
    exact Finset.sum_pos' (fun i _ => sq_nonneg (SKP.fusionBasis.fpdim i))
      ⟨SKP.fusionBasis.one, Finset.mem_univ _, pow_pos (SKP.fusionBasis.fpdim_pos _) _⟩
  have hn : SN.fusionBasis.totalFPdim =
      SB.fusionBasis.totalFPdim * (2 * SignKernel.positiveTotalFPdim SK χ) := by
    rw [← htwo.1]
    exact ((eq_div_iff hb).mp hk).symm.trans (mul_comm _ _)
  rw [hn, htwo.2, hi]
  field_simp [hb, hq]
  <;> ring

end Paper18.Category.CategoricalCaseTwo
