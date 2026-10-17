import Paper18.Category.SignKernelCenterIdentification

/-! # Intrinsic dimensions of the actual sign kernel and its center -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.SignKernel
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts C] [HasKernels C] [RightRigidCategory C]
  [Simple (𝟙_ C)] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- Support dimensions of a full fusion subcategory are the actual ambient
support dimensions of the intersection. -/
lemma fullSubcategory_supportFPdim_eq (P : ObjectProperty C)
    [IsAdditiveFullProperty P] [P.IsMonoidal] (Q : ObjectProperty C) :
    (letI := S.fullSubcategoryHasKernels P
     letI := S.fullSubcategoryRightRigid P
     letI := S.fullSubcategorySimpleUnit P
     (S.fullSubcategorySkeleton P).supportFPdim (fun X => Q X.obj)) =
      S.supportFPdim (fun X => P X ∧ Q X) := by
  letI := S.fullSubcategoryHasKernels P
  letI := S.fullSubcategoryRightRigid P
  letI := S.fullSubcategorySimpleUnit P
  let T := S.fullSubcategorySkeleton P
  have hd (i : {i : ι // P (S.simpleObject i)}) :
      T.fusionBasis.fpdim i = S.fusionBasis.fpdim i.val := by
    rw [← T.fpdim_simple]
    exact (S.fullSubcategoryFPdim_eq P (T.simpleObject i)).trans (S.fpdim_simple i.val)
  change (∑ i : {i : ι // P (S.simpleObject i)},
      if Q (S.simpleObject i.val) then T.fusionBasis.fpdim i ^ 2 else 0) = _
  simp_rw [hd]
  unfold FiniteSemisimpleSkeleton.supportFPdim
  dsimp only
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i => P (S.simpleObject i)),
        if Q (S.simpleObject i) then S.fusionBasis.fpdim i ^ 2 else 0 :=
      (Finset.sum_subtype (Finset.univ.filter (fun i => P (S.simpleObject i)))
        (fun i => by simp) (fun i =>
          if Q (S.simpleObject i) then S.fusionBasis.fpdim i ^ 2 else 0)).symm
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hp : P (S.simpleObject i) <;> simp [hp]

variable [BraidedCategory C]
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]

/-- Intrinsic total FP dimension of the actual transparent center of the
actual positive full fusion subcategory. -/
def positiveCenterFPdim : ℝ :=
  letI := hasKernels χ S
  letI := rightRigid χ S
  letI := simpleUnit χ S
  (skeleton χ S).centralizerFPdim (Set.univ : Set (Positive χ))

variable (hχ : ∀ X : C, χ.hom.app X ≫ χ.hom.app X = 𝟙 X)

include hχ in
lemma positiveCenterFPdim_eq_support_of_nontrivial_center (X : C)
    (hZ : X ∈ mugerCenter) (hX : χ.hom.app X ≠ 𝟙 X) :
    positiveCenterFPdim S χ =
      S.supportFPdim (fun Y => Y ∈ mugerCenter ∧ positiveProperty χ Y) := by
  letI := hasKernels χ S
  letI := rightRigid χ S
  letI := simpleUnit χ S
  let T := skeleton χ S
  have he : centralizerProperty (Set.univ : Set (Positive χ)) =
      (fun Z : Positive χ => Z.obj ∈ mugerCenter) := by
    funext Z
    exact propext (transparent_iff_ambient_of_nontrivial_center χ S hχ X hZ hX Z)
  change T.supportFPdim (centralizerProperty (Set.univ : Set (Positive χ))) = _
  rw [he]
  calc
    _ = S.supportFPdim (fun Y => positiveProperty χ Y ∧ Y ∈ mugerCenter) :=
      fullSubcategory_supportFPdim_eq S (positiveProperty χ)
        (centralizerProperty (Set.univ : Set C))
    _ = _ := by
      unfold FiniteSemisimpleSkeleton.supportFPdim
      apply Finset.sum_congr rfl
      intro i _
      dsimp only
      rw [and_comm]

include hχ in
/-- The actual positive fusion category has half the ambient total dimension,
and its actual transparent center has half the ambient center dimension. -/
theorem total_and_center_indexTwo (X : C) (hZ : X ∈ mugerCenter)
    (hX : χ.hom.app X ≠ 𝟙 X) :
    S.fusionBasis.totalFPdim = 2 * positiveTotalFPdim S χ ∧
      S.centralizerFPdim (Set.univ : Set C) = 2 * positiveCenterFPdim S χ := by
  constructor
  · exact totalFPdim_indexTwo_of_nontrivial S χ hχ X hX
  · rw [positiveCenterFPdim_eq_support_of_nontrivial_center S χ hχ X hZ hX]
    exact center_restriction_indexTwo χ S hχ X hZ hX

end Paper18.Category.SignKernel
