import Paper18.Category.RelativeCenterDimension
import Paper18.Category.RelativeCenterFactorizationBasic

/-! # Genuine FP-dimension product for actual categorical centralizers -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)] [BraidedCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {P : ObjectProperty C} [P.IsMonoidal] [IsAdditiveFullProperty P]
  {ι : Type w} [Fintype ι]
namespace RelativeCenter
open Drinfeld

/-- The actual canonical factorization followed by actual restriction. -/
def factorization (P : ObjectProperty C) [P.IsMonoidal] : DeligneProduct C C ⥤ RelativeCenter P :=
  Drinfeld.deligneFactorization C ⋙ restriction P

instance factorization_monoidal : (factorization P).Monoidal := by unfold factorization; infer_instance
instance factorization_additive : (factorization P).Additive := by unfold factorization; infer_instance
instance factorization_linear : (factorization P).Linear ℂ := by unfold factorization; infer_instance

def factorizationPairIso (X Y : C) :
    (factorization P).obj ((Mat_.embedding (LinearTensor C C)).obj ⟨X,Y⟩) ≅
      (positive P).obj X ⊗ (negative P).obj Y :=
  (restriction P).mapIso (Drinfeld.deligneFactorizationPairIso X Y)

variable (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

include S J in
/-- Nondegenerate ambient factorization and the constructed relative
averaging retract make the actual relative factorization dominant. -/
lemma factorization_dominant (hC : IsNondegenerate (C := C)) (Z : RelativeCenter P) :
    ∃ A : DeligneProduct C C, Nonempty (Retract Z ((factorization P).obj A)) := by
  let E := Drinfeld.factorizationEquivalence S J hC
  let W := inductionObj S J Z.1
  refine ⟨E.inverse.obj W, ⟨(restrictionRetract S J Z).trans ?_⟩⟩
  exact Retract.ofIso ((restriction P).mapIso (E.counitIso.app W).symm)

section Index
variable [HasKernels (DeligneProduct C C)] [Simple (𝟙_ (DeligneProduct C C))]
  [RightRigidCategory (RelativeCenter P)]

/-- The actual relative factorization has unit multiplicity exactly on
centralizing dual pairs. This is derived from actual rigid Hom rotation. -/
lemma factorization_imageCoeff (i j : ι) :
    (DeligneProduct.skeleton S S).imageCoeff (skeleton (P := P) S J) (factorization P)
      (i,j) (skeleton (P := P) S J).unitLabel =
      if S.dualLabel i = j ∧ S.simpleObject j ∈ centralizer (P : Set C) then 1 else 0 := by
  let T := skeleton (P := P) S J
  change Module.finrank ℂ (T.simpleObject T.unitLabel ⟶
    (factorization P).obj (DeligneProduct.pairObject S S i j)) = _
  change Module.finrank ℂ (T.simpleObject T.unitLabel ⟶
    (factorization P).obj ((Mat_.embedding (LinearTensor C C)).obj
      ⟨S.simpleObject i, S.simpleObject j⟩)) = _
  rw [finrank_hom_iso T.unitIso (factorizationPairIso (P := P) (S.simpleObject i) (S.simpleObject j))]
  exact finrank_unit_positive_negative S i j

lemma factorization_unit_index :
    (∑ p, ((DeligneProduct.skeleton S S).imageCoeff (skeleton (P := P) S J) (factorization P)
      p (skeleton (P := P) S J).unitLabel : ℝ) *
        (DeligneProduct.skeleton S S).fusionBasis.fpdim p) = S.centralizerFPdim (P : Set C) := by
  simp_rw [factorization_imageCoeff S J, DeligneProduct.fpdim_pair,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  change (∑ j, ∑ i, (if S.dualLabel i = j ∧ S.simpleObject j ∈ centralizer (P : Set C)
      then 1 else 0) * (S.fusionBasis.fpdim i * S.fusionBasis.fpdim j)) =
    ∑ j, if S.simpleObject j ∈ centralizer (P : Set C) then S.fusionBasis.fpdim j ^ 2 else 0
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : S.simpleObject j ∈ centralizer (P : Set C)
  · simp only [hj, and_true, if_true]
    have he (i : ι) : S.dualLabel i = j ↔ i = S.dualLabel j := by
      constructor
      · intro h
        simpa only [S.dualLabel_involutive] using congrArg S.dualLabel h
      · intro h
        rw [h, S.dualLabel_involutive]
    simp_rw [he]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    change S.fusionBasis.fpdim (S.fusionBasis.dual j) * S.fusionBasis.fpdim j = _
    rw [S.fusionBasis.fpdim_dual, pow_two]
  · simp only [hj, and_false, if_false, zero_mul, Finset.sum_const_zero]

end Index

include J in
/-- The genuine relative factorization quotient computes the actual FP
centralizer dimension. No pivotal positivity or numerical dimension law is an input. -/
lemma centralizerFPdim_mul (hC : IsNondegenerate (C := C)) :
    S.supportFPdim P * S.centralizerFPdim (P : Set C) = S.fusionBasis.totalFPdim := by
  letI := DeligneProduct.hasKernels S S
  letI := DeligneProduct.simpleUnit S S
  letI := rightRigidCategory (P := P) S J
  have h := (DeligneProduct.skeleton S S).dominant_totalFPdim_eq
    (skeleton (P := P) S J) (factorization P) (factorization_dominant S J hC)
  rw [DeligneProduct.totalFPdim_product, factorization_unit_index,
    totalFPdim (P := P) S J] at h
  have hpos : 0 < S.fusionBasis.totalFPdim :=
    Finset.sum_pos' (fun i _ => sq_nonneg (S.fusionBasis.fpdim i))
      ⟨S.fusionBasis.one, Finset.mem_univ _, pow_pos (S.fusionBasis.fpdim_pos _) _⟩
  apply mul_right_cancel₀ (ne_of_gt hpos)
  calc
    (S.supportFPdim P * S.centralizerFPdim (P : Set C)) * S.fusionBasis.totalFPdim =
        S.centralizerFPdim (P : Set C) * (S.supportFPdim P * S.fusionBasis.totalFPdim) := by ring
    _ = _ := h.symm

end RelativeCenter
namespace FiniteSemisimpleSkeleton
variable (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

include J in
/-- The actual fusion-subcategory FP dimension times its actual categorical
centralizer FP dimension is the ambient FP dimension in a genuine Müger
nondegenerate braided pivotal fusion category. -/
theorem supportFPdim_mul_centralizer (hC : IsNondegenerate (C := C))
    (P : ObjectProperty C) [P.IsMonoidal] [IsAdditiveFullProperty P] :
    S.supportFPdim P * S.centralizerFPdim (P : Set C) = S.fusionBasis.totalFPdim :=
  RelativeCenter.centralizerFPdim_mul (P := P) S J hC

end FiniteSemisimpleSkeleton
end Paper18.Category
