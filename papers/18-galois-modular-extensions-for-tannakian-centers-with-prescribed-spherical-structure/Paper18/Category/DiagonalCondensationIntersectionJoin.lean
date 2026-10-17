import Paper18.Category.DiagonalCondensationEmbeddingCentralizer
import Paper18.Category.CentralizerJoinDimension
import Paper18.Category.FusionJoinIntegral

/-! # Actual equality of the condensed centralizer and the generated join

Actual centralization gives the inclusion of the join. Its proved categorical
join/intersection dimension formula, combined with the computed condensation
dimension identity, excludes every missing simple constituent.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w vB uB
namespace Paper18.Category.DiagonalCondensation
variable {M : Type u} [Category.{v} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M]
  [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory M] [MonoidalPreadditive M] [MonoidalLinear ℂ M]
  [RightRigidCategory M] [Simple (𝟙_ M)] [BraidedCategory M]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton M ι)
  (J : PivotalStructure M) (hM : IsNondegenerate (C := M))
  (P Q : ObjectProperty M) [IsAdditiveFullProperty P] [P.IsMonoidal]
  [IsAdditiveFullProperty Q] [Q.IsMonoidal]
  {B : Type uB} [Category.{vB} B] (H : B ⥤ M)

/-- The actual intersection contains the tensor unit, so its support FP
dimension is positive. -/
lemma supportFPdim_inter_pos : 0 < S.supportFPdim (fun X => P X ∧ Q X) := by
  unfold FiniteSemisimpleSkeleton.supportFPdim
  apply Finset.sum_pos'
  · intro i hi
    split_ifs <;> positivity
  · refine ⟨S.unitLabel, Finset.mem_univ _, ?_⟩
    have hp : P (S.simpleObject S.unitLabel) :=
      IsAdditiveFullProperty.of_iso P S.unitIso (ObjectProperty.prop_unit P)
    have hq : Q (S.simpleObject S.unitLabel) :=
      IsAdditiveFullProperty.of_iso Q S.unitIso (ObjectProperty.prop_unit Q)
    simp only [hp, hq, and_self, if_true]
    exact pow_pos (S.fusionBasis.fpdim_pos _) 2

include S J hM in
/-- Actual centralization of both generating categories places their actual
fusion join in the actual centralizer of the embedded category. -/
lemma fusionJoin_le_image_centralizer
    (hP : ∀ X, P X → ∀ Y, Centralizes X (H.obj Y))
    (hQ : ∀ X, Q X → ∀ Y, Centralizes X (H.obj Y)) :
    ∀ X, fusionJoin P Q X → X ∈ centralizer (Set.range H.obj) := by
  apply (S.fusionJoin_le_iff J hM P Q (centralizerProperty (Set.range H.obj))).mpr
  constructor
  · intro X hX Y hY
    obtain ⟨Z, rfl⟩ := hY
    exact hP X hX Z
  · intro X hX Y hY
    obtain ⟨Z, rfl⟩ := hY
    exact hQ X hX Z

include J hM in
/-- The actual computed centralizer product dimension identifies the actual
centralizer with the actual generated fusion subcategory. The join formula
and the missing-simple exclusion are both categorical theorems. -/
lemma fusionJoin_eq_image_centralizer_of_product_dimension
    (hP : ∀ X, P X → ∀ Y, Centralizes X (H.obj Y))
    (hQ : ∀ X, Q X → ∀ Y, Centralizes X (H.obj Y))
    (hd : S.centralizerFPdim (Set.range H.obj) *
      S.supportFPdim (fun X => P X ∧ Q X) = S.supportFPdim P * S.supportFPdim Q) :
    fusionJoin P Q = centralizerProperty (Set.range H.obj) := by
  have hj := S.supportFPdim_join_mul_inter J hM P Q
  have he : S.supportFPdim (fusionJoin P Q) = S.centralizerFPdim (Set.range H.obj) :=
    mul_right_cancel₀ (ne_of_gt (supportFPdim_inter_pos S P Q)) (hj.trans hd.symm)
  exact (S.supportFPdim_eq_iff_of_le (fusionJoin P Q)
    (centralizerProperty (Set.range H.obj))
    (fusionJoin_le_image_centralizer S J hM P Q H hP hQ)).mp he

include J hM in
/-- Integrality of the two actual generators and the computed actual
condensation dimension prove integrality of the whole actual centralizer. -/
lemma imageCentralizer_integral_of_product_dimension
    (hP : ∀ X, P X → ∀ Y, Centralizes X (H.obj Y))
    (hQ : ∀ X, Q X → ∀ Y, Centralizes X (H.obj Y))
    (hd : S.centralizerFPdim (Set.range H.obj) *
      S.supportFPdim (fun X => P X ∧ Q X) = S.supportFPdim P * S.supportFPdim Q)
    (hPI : S.FullSubcategoryIntegral P) (hQI : S.FullSubcategoryIntegral Q) :
    S.FullSubcategoryIntegral (centralizerProperty (Set.range H.obj)) := by
  apply (S.fullSubcategoryIntegral_iff (centralizerProperty (Set.range H.obj))).mpr
  have hi := (S.fullSubcategoryIntegral_iff (fusionJoin P Q)).mp
    (S.fusionJoinIntegral J P Q hM hPI hQI)
  intro i hx
  apply hi i
  rw [fusionJoin_eq_image_centralizer_of_product_dimension S J hM P Q H hP hQ hd]
  exact hx

end Paper18.Category.DiagonalCondensation
