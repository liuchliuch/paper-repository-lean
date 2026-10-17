import Paper18.Category.CentralizerJoinDimension
import Paper18.Category.RelativeCenterCentralizerDimension

/-! # FP dimension reciprocity for actual centralizer intersections -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.FiniteSemisimpleSkeleton
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [BraidedCategory C]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- Every actual full fusion subcategory has strictly positive FP dimension,
because its actual tensor unit is among its actual simple constituents. -/
lemma supportFPdim_pos_of_monoidal (P : ObjectProperty C)
    [P.IsMonoidal] [IsAdditiveFullProperty P] : 0 < S.supportFPdim P := by
  have hu : P (S.simpleObject S.unitLabel) :=
    IsAdditiveFullProperty.of_iso P S.unitIso (ObjectProperty.prop_unit P)
  apply Finset.sum_pos'
  · intro i _
    split_ifs <;> positivity
  · exact ⟨S.unitLabel, Finset.mem_univ _, by
      rw [if_pos hu]
      exact pow_pos (S.fusionBasis.fpdim_pos _) 2⟩

/-- Actual centralizer-intersection reciprocity inside a nondegenerate
braided fusion category. Both full subcategories are arbitrary. -/
lemma supportFPdim_centralizer_inter_reciprocity (J : PivotalStructure C)
    (hC : IsNondegenerate (C := C)) (P Q : ObjectProperty C)
    [P.IsMonoidal] [Q.IsMonoidal]
    [IsAdditiveFullProperty P] [IsAdditiveFullProperty Q] :
    S.supportFPdim Q * S.supportFPdim (fun X => P X ∧ centralizerProperty (Q : Set C) X) =
      S.supportFPdim P * S.supportFPdim (fun X => Q X ∧ centralizerProperty (P : Set C) X) := by
  let R := centralizerProperty (P : Set C)
  have hc : centralizerProperty (fusionJoin Q R : Set C) =
      (fun X => P X ∧ centralizerProperty (Q : Set C) X) := by
    funext X
    apply propext
    change X ∈ centralizer (fusionJoin Q R : Set C) ↔ _
    rw [centralizer_fusionJoin]
    change (X ∈ centralizer (Q : Set C) ∧ X ∈ centralizer (centralizer (P : Set C))) ↔ _
    rw [S.double_centralizer_eq J hC P]
    exact and_comm
  have hj := S.supportFPdim_join_mul_inter J hC Q R
  have hl := S.supportFPdim_mul_centralizer J hC (fusionJoin Q R)
  change S.supportFPdim (fusionJoin Q R) *
    S.supportFPdim (centralizerProperty (fusionJoin Q R : Set C)) = _ at hl
  rw [hc] at hl
  have hp := S.supportFPdim_mul_centralizer J hC P
  have hn : S.supportFPdim R ≠ 0 := ne_of_gt (S.supportFPdim_pos_of_monoidal R)
  apply mul_left_cancel₀ hn
  linear_combination
    -S.supportFPdim (fun X => P X ∧ centralizerProperty (Q : Set C) X) * hj +
      S.supportFPdim (fun X => Q X ∧ R X) * hl -
      S.supportFPdim (fun X => Q X ∧ R X) * hp

end Paper18.Category.FiniteSemisimpleSkeleton
