import Paper18.Category.CentralizerDimensionProjector

/-! # Intrinsic dimensions and positive support of actual fusion subcategories -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.FiniteSemisimpleSkeleton
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- The positive weighted simple support of an actual object property. -/
def supportFPdim (P : ObjectProperty C) : ℝ :=
  ∑ i, if P (S.simpleObject i) then S.fusionBasis.fpdim i ^ 2 else 0

lemma supportFPdim_nonneg (P : ObjectProperty C) : 0 ≤ S.supportFPdim P := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> positivity

lemma supportFPdim_mono {P Q : ObjectProperty C} (h : ∀ X, P X → Q X) :
    S.supportFPdim P ≤ S.supportFPdim Q := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hp : P (S.simpleObject i)
  · simp only [if_pos hp, if_pos (h _ hp)]
    exact le_rfl
  · simp only [if_neg hp]
    split_ifs <;> positivity

lemma supportFPdim_le_total (P : ObjectProperty C) :
    S.supportFPdim P ≤ S.fusionBasis.totalFPdim := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> first | exact le_rfl | positivity

/-- Every missing actual simple causes a strict dimension gap. -/
lemma supportFPdim_lt_of_missing {P Q : ObjectProperty C} (h : ∀ X, P X → Q X)
    (i : ι) (hQ : Q (S.simpleObject i)) (hP : ¬ P (S.simpleObject i)) :
    S.supportFPdim P < S.supportFPdim Q := by
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hp : P (S.simpleObject j)
    · simp only [if_pos hp, if_pos (h _ hp)]
      exact le_rfl
    · simp only [if_neg hp]
      split_ifs <;> positivity
  · exact ⟨i, Finset.mem_univ _, by
      simp only [if_pos hQ, if_neg hP]
      exact pow_pos (S.fusionBasis.fpdim_pos i) 2⟩

/-- With actual summand and biproduct closure, equality of positive support
dimensions under inclusion forces equality on every actual object. -/
lemma supportFPdim_eq_iff_of_le (P Q : ObjectProperty C)
    [IsAdditiveFullProperty P] [IsAdditiveFullProperty Q]
    (h : ∀ X, P X → Q X) :
    S.supportFPdim P = S.supportFPdim Q ↔ P = Q := by
  constructor
  · intro hd
    have hs (i : ι) : P (S.simpleObject i) ↔ Q (S.simpleObject i) := by
      refine ⟨h _, fun hq => ?_⟩
      by_contra hp
      exact (ne_of_lt (S.supportFPdim_lt_of_missing h i hq hp)) hd
    funext X
    apply propext
    rw [S.property_iff_labels P X, S.property_iff_labels Q X]
    exact forall_congr' (fun a => hs (S.label X a))
  · rintro rfl
    rfl

/-- The positive support is exactly the intrinsic total FP dimension of the
actual inherited full fusion category. -/
lemma fullSubcategory_totalFPdim_eq (P : ObjectProperty C)
    [IsAdditiveFullProperty P] [P.IsMonoidal] :
    (letI := S.fullSubcategoryHasKernels P
     letI := S.fullSubcategoryRightRigid P
     letI := S.fullSubcategorySimpleUnit P
     (S.fullSubcategorySkeleton P).fusionBasis.totalFPdim) = S.supportFPdim P := by
  letI := S.fullSubcategoryHasKernels P
  letI := S.fullSubcategoryRightRigid P
  letI := S.fullSubcategorySimpleUnit P
  let T := S.fullSubcategorySkeleton P
  have hd (i : {i : ι // P (S.simpleObject i)}) :
      T.fusionBasis.fpdim i = S.fusionBasis.fpdim i.val := by
    rw [← T.fpdim_simple]
    exact (S.fullSubcategoryFPdim_eq P (T.simpleObject i)).trans (S.fpdim_simple i.val)
  change (∑ i, T.fusionBasis.fpdim i ^ 2) = _
  simp_rw [hd]
  rw [supportFPdim, ← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter (fun i => P (S.simpleObject i)))
    (fun i => by simp) (fun i => S.fusionBasis.fpdim i ^ 2)).symm

lemma supportFPdim_inter_add_union (P Q : ObjectProperty C) :
    S.supportFPdim (fun X => P X ∧ Q X) + S.supportFPdim (fun X => P X ∨ Q X) =
      S.supportFPdim P + S.supportFPdim Q := by
  simp only [supportFPdim, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

variable [BraidedCategory C]

/-- Total dimension of the actual categorical centralizer, computed by its
actual simple support. The preceding theorem identifies this with its
intrinsic fusion-category dimension. -/
abbrev centralizerFPdim (T : Set C) : ℝ := S.supportFPdim (centralizerProperty T)

lemma centralizerFPdim_eq_intrinsic (T : Set C) :
    S.centralizerFPdim T =
      (letI := S.fullSubcategoryHasKernels (centralizerProperty T)
       letI := S.fullSubcategoryRightRigid (centralizerProperty T)
       letI := S.fullSubcategorySimpleUnit (centralizerProperty T)
       (S.centralizerSkeleton T).fusionBasis.totalFPdim) :=
  (S.fullSubcategory_totalFPdim_eq (centralizerProperty T)).symm

lemma centralizerFPdim_antitone {T V : Set C} (h : T ⊆ V) :
    S.centralizerFPdim V ≤ S.centralizerFPdim T :=
  S.supportFPdim_mono (fun _ hx => centralizer_antitone h hx)

end Paper18.Category.FiniteSemisimpleSkeleton
