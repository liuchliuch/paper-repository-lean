import Paper18.Category.DiagonalCondensationIntersectionJoin
import Paper18.Category.FusionJoinIntegralImage
import Paper18.Category.RelativeTensorCentralDimensionBasic

/-! # Integrality of the actual condensed centralizer from actual images -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w vE uE wE vI uI wI vB uB
namespace Paper18.Category.DiagonalCondensation
variable {M : Type u} [Category.{v} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M]
  [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory M] [MonoidalPreadditive M] [MonoidalLinear ℂ M]
  [RightRigidCategory M] [Simple (𝟙_ M)] [BraidedCategory M]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton M ι)
  (J : PivotalStructure M) (hM : IsNondegenerate (C := M))
  {E : Type uE} [Category.{vE} E] [Preadditive E] [Linear ℂ E]
  [HasKernels E] [HasFiniteBiproducts E]
  [∀ X Y : E, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalLinear ℂ E]
  [RightRigidCategory E] [Simple (𝟙_ E)]
  {κ : Type wE} [Fintype κ] (T : FiniteSemisimpleSkeleton E κ)
  {I : Type uI} [Category.{vI} I] [Preadditive I] [Linear ℂ I]
  [HasKernels I] [HasFiniteBiproducts I]
  [∀ X Y : I, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory I] [MonoidalPreadditive I] [MonoidalLinear ℂ I]
  [RightRigidCategory I] [Simple (𝟙_ I)]
  {ν : Type wI} [Fintype ν] (U : FiniteSemisimpleSkeleton I ν)
  (F : E ⥤ M) [F.Monoidal] [F.Additive] [F.Linear ℂ] [F.Full] [F.Faithful]
  (G : I ⥤ M) [G.Monoidal] [G.Additive] [G.Linear ℂ] [G.Full] [G.Faithful]
  {B : Type uB} [Category.{vB} B] (H : B ⥤ M)

include J hM T U in
/-- Actual integral source categories, actual centralization and the computed
condensation product identity give both the genuine centralizer/join equality
and actual integrality. Actual source FP dimensions replace support dimensions
by the proved fully faithful image theorem. -/
theorem imageCentralizer_eq_join_and_integral
    (hF : ∀ X Y, Centralizes (F.obj X) (H.obj Y))
    (hG : ∀ X Y, Centralizes (G.obj X) (H.obj Y))
    (hd : S.centralizerFPdim (Set.range H.obj) *
      S.supportFPdim (fun X => F.essImage X ∧ G.essImage X) =
        T.fusionBasis.totalFPdim * U.fusionBasis.totalFPdim)
    (hT : T.Integral) (hU : U.Integral) :
    fusionJoin F.essImage G.essImage = centralizerProperty (Set.range H.obj) ∧
      S.FullSubcategoryIntegral (centralizerProperty (Set.range H.obj)) := by
  have hp : ∀ X, F.essImage X → ∀ Y, Centralizes X (H.obj Y) := by
    intro X hX Y
    exact (hF hX.witness Y).of_iso_left hX.getIso.symm
  have hq : ∀ X, G.essImage X → ∀ Y, Centralizes X (H.obj Y) := by
    intro X hX Y
    exact (hG hX.witness Y).of_iso_left hX.getIso.symm
  have hd' : S.centralizerFPdim (Set.range H.obj) *
      S.supportFPdim (fun X => F.essImage X ∧ G.essImage X) =
        S.supportFPdim F.essImage * S.supportFPdim G.essImage := by
    rw [RelativeTensor.supportFPdim_essImage T S F, RelativeTensor.supportFPdim_essImage U S G]
    exact hd
  exact ⟨fusionJoin_eq_image_centralizer_of_product_dimension S J hM
      F.essImage G.essImage H hp hq hd',
    imageCentralizer_integral_of_product_dimension S J hM F.essImage G.essImage H hp hq hd'
      (T.essImageIntegral S F hT) (U.essImageIntegral S G hU)⟩

end Paper18.Category.DiagonalCondensation
