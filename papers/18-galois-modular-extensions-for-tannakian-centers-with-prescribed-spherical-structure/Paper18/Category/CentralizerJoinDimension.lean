import Paper18.Category.CentralizerJoinImage

/-! # Genuine FP dimensions of joins and intersections -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts C] [HasKernels C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [RightRigidCategory C] [Simple (𝟙_ C)] {ι : Type w} [Fintype ι]
namespace FusionJoin

lemma sum_subtype_indicator {α : Type w} [Fintype α] (p : α → Prop) (f : α → ℝ) :
    (∑ i : {i // p i}, f i.val) = ∑ i, if p i then f i else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter p) (fun i => by simp) f).symm

/-- The unit multiplicity in an actual tensor of two chosen simple
representatives is the actual dual Kronecker delta. -/
lemma finrank_unit_tensor (S : FiniteSemisimpleSkeleton C ι) (i j : ι) :
    Module.finrank ℂ ((𝟙_ C) ⟶ S.simpleObject i ⊗ S.simpleObject j) =
      if S.dualLabel i = j then 1 else 0 := by
  calc
    _ = Module.finrank ℂ ((S.simpleObject i)ᘁ ⊗ (𝟙_ C) ⟶ S.simpleObject j) :=
      (tensorLeftHomLinearEquiv (𝟙_ C) (S.simpleObject i) ((S.simpleObject i)ᘁ)
        (S.simpleObject j)).finrank_eq.symm
    _ = Module.finrank ℂ (S.simpleObject (S.dualLabel i) ⟶ S.simpleObject j) :=
      finrank_hom_iso ((ρ_ ((S.simpleObject i)ᘁ)) ≪≫ (S.dualIso i).symm) (Iso.refl _)
    _ = _ := S.finrank_simple_hom_simple _ _

end FusionJoin
namespace FiniteSemisimpleSkeleton
variable (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

include J in
/-- The product of the actual join and intersection FP dimensions is the
product of the two actual full fusion-subcategory FP dimensions. Actual
tensor-image dominance and actual rigid Hom rotation supply the dimension
calculation; no join dimension identity is assumed. -/
theorem supportFPdim_join_mul_inter (hC : IsNondegenerate (C := C))
    (P Q : ObjectProperty C) [P.IsMonoidal] [Q.IsMonoidal]
    [IsAdditiveFullProperty P] [IsAdditiveFullProperty Q] :
    S.supportFPdim (fusionJoin P Q) * S.supportFPdim (fun X => P X ∧ Q X) =
      S.supportFPdim P * S.supportFPdim Q := by
  letI := S.fullSubcategoryHasKernels P
  letI := S.fullSubcategoryHasKernels Q
  letI := S.fullSubcategoryRightRigid P
  letI := S.fullSubcategoryRightRigid Q
  letI := S.fullSubcategorySimpleUnit P
  letI := S.fullSubcategorySimpleUnit Q
  let SP := S.fullSubcategorySkeleton P
  let SQ := S.fullSubcategorySkeleton Q
  letI := DeligneProduct.hasKernels SP SQ
  letI := DeligneProduct.simpleUnit SP SQ
  letI := S.fullSubcategoryHasKernels (fusionJoin P Q)
  letI := S.fullSubcategoryRightRigid (fusionJoin P Q)
  letI := S.fullSubcategorySimpleUnit (fusionJoin P Q)
  let T := S.fullSubcategorySkeleton (fusionJoin P Q)
  let B := DeligneProduct.skeleton SP SQ
  let F := FusionJoin.tensorToJoin P Q
  have hm (i : {i // P (S.simpleObject i)}) (j : {j // Q (S.simpleObject j)}) :
      B.imageCoeff T F (i,j) T.unitLabel = if S.dualLabel i.val = j.val then 1 else 0 := by
    change Module.finrank ℂ ((T.simpleObject T.unitLabel).obj ⟶
      (FusionJoin.tensorFunctor P Q).obj (DeligneProduct.pairObject SP SQ i j)) = _
    change Module.finrank ℂ ((T.simpleObject T.unitLabel).obj ⟶
      (FusionJoin.tensorFunctor P Q).obj ((Mat_.embedding _).obj ⟨SP.simpleObject i,SQ.simpleObject j⟩)) = _
    calc
      _ = Module.finrank ℂ ((𝟙_ C) ⟶ S.simpleObject i.val ⊗ S.simpleObject j.val) :=
        finrank_hom_iso ((fusionJoin P Q).ι.mapIso T.unitIso)
          (FusionJoin.tensorPairIso P Q (SP.simpleObject i) (SQ.simpleObject j))
      _ = _ := FusionJoin.finrank_unit_tensor S i.val j.val
  have hdP (i : {i // P (S.simpleObject i)}) :
      SP.fusionBasis.fpdim i = S.fusionBasis.fpdim i.val := by
    rw [← SP.fpdim_simple]
    exact (S.fullSubcategoryFPdim_eq P (SP.simpleObject i)).trans (S.fpdim_simple i.val)
  have hdQ (j : {j // Q (S.simpleObject j)}) :
      SQ.fusionBasis.fpdim j = S.fusionBasis.fpdim j.val := by
    rw [← SQ.fpdim_simple]
    exact (S.fullSubcategoryFPdim_eq Q (SQ.simpleObject j)).trans (S.fpdim_simple j.val)
  have hdual (i : ι) : Q (S.simpleObject (S.dualLabel i)) ↔ Q (S.simpleObject i) := by
    constructor
    · intro h
      simpa only [S.dualLabel_involutive] using S.property_dualLabel Q (S.dualLabel i) h
    · exact S.property_dualLabel Q i
  have hindex : (∑ p, (B.imageCoeff T F p T.unitLabel : ℝ) * B.fusionBasis.fpdim p) =
      S.supportFPdim (fun X => P X ∧ Q X) := by
    change (∑ p, (B.imageCoeff T F p T.unitLabel : ℝ) *
      (DeligneProduct.skeleton SP SQ).fusionBasis.fpdim p) = _
    simp_rw [DeligneProduct.fpdim_pair, hm, hdP, hdQ, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Fintype.sum_prod_type]
    have hrow (i : ι) :
        (∑ j : {j // Q (S.simpleObject j)},
          (if S.dualLabel i = j.val then 1 else 0) *
            (S.fusionBasis.fpdim i * S.fusionBasis.fpdim j.val)) =
          if Q (S.simpleObject i) then S.fusionBasis.fpdim i ^ 2 else 0 := by
      rw [FusionJoin.sum_subtype_indicator (fun j => Q (S.simpleObject j))
        (fun j => (if S.dualLabel i = j then 1 else 0) *
          (S.fusionBasis.fpdim i * S.fusionBasis.fpdim j))]
      rw [Finset.sum_eq_single (S.dualLabel i)]
      · simp only [hdual, if_true]
        have hd : S.fusionBasis.fpdim (S.dualLabel i) = S.fusionBasis.fpdim i :=
          S.fusionBasis.fpdim_dual i
        simp only [hd, one_mul, pow_two]
      · intro j _ hj
        simp only [Ne.symm hj, if_false, zero_mul, ite_self]
      · simp
    simp_rw [hrow]
    rw [FusionJoin.sum_subtype_indicator (fun i => P (S.simpleObject i))
      (fun i => if Q (S.simpleObject i) then S.fusionBasis.fpdim i ^ 2 else 0)]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hp : P (S.simpleObject i) <;> by_cases hq : Q (S.simpleObject i) <;>
      simp only [hp, hq, and_self, and_false, and_true, if_true, if_false]
  have h := B.dominant_totalFPdim_eq T F (FusionJoin.tensorToJoin_dominant P Q S J hC)
  rw [hindex] at h
  change (DeligneProduct.skeleton SP SQ).fusionBasis.totalFPdim = _ at h
  rw [DeligneProduct.totalFPdim_product, S.fullSubcategory_totalFPdim_eq P,
    S.fullSubcategory_totalFPdim_eq Q, S.fullSubcategory_totalFPdim_eq (fusionJoin P Q)] at h
  exact (mul_comm _ _).trans h.symm

end FiniteSemisimpleSkeleton
end Paper18.Category
