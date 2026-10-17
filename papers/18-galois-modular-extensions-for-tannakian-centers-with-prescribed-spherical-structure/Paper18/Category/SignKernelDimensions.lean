import Paper18.Category.SignKernelBasic
import Paper18.Category.CentralizerDimensionBasic
import Paper18.Fusion.Grading

/-! # Index two of the actual kernel of a nontrivial involutive character -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.FusionBasis
variable {ι : Type w} [Fintype ι] (B : FusionBasis ι)

/-- A nontrivial sign grading has zero signed regular FP mass. This follows
from the actual fusion dimension and reciprocity equations. -/
lemma signed_fpdim_sum_zero (r : ι → ℝ) (hr : ∀ i, r i = 1 ∨ r i = -1)
    (hm : ∀ i j k, 0 < B.N i j k → r k = r i * r j)
    (a : ι) (ha : r a = -1) : ∑ i, r i * B.fpdim i ^ 2 = 0 := by
  let M := ∑ i, r i * B.fpdim i ^ 2
  have hcol (j : ι) : ∑ i, (B.N a i j : ℝ) * B.fpdim i = B.fpdim a * B.fpdim j := by
    simp_rw [B.N_dual a]
    rw [B.fpdim_mul, B.fpdim_dual]
  have ht (i j : ι) :
      r i * B.fpdim i * ((B.N a i j : ℝ) * B.fpdim j) =
        r a * r j * B.fpdim j * ((B.N a i j : ℝ) * B.fpdim i) := by
    by_cases hn : B.N a i j = 0
    · simp [hn]
    · have hij := hm a i j (Nat.pos_of_ne_zero hn)
      have hs : r a * r a = 1 := by rcases hr a with h | h <;> simp [h]
      have hi : r i = r a * r j := by rw [hij, ← mul_assoc, hs, one_mul]
      rw [hi]
      ring
  have hb : B.fpdim a * M = r a * B.fpdim a * M := by
    calc
      _ = ∑ i, r i * B.fpdim i * (B.fpdim a * B.fpdim i) := by
        simp only [M, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i, ∑ j, r i * B.fpdim i * ((B.N a i j : ℝ) * B.fpdim j) := by
        simp_rw [← B.fpdim_mul a, Finset.mul_sum]
      _ = ∑ j, ∑ i, r a * r j * B.fpdim j * ((B.N a i j : ℝ) * B.fpdim i) := by
        simp_rw [ht]
        rw [Finset.sum_comm]
      _ = ∑ j, r a * r j * B.fpdim j * (B.fpdim a * B.fpdim j) := by
        simp_rw [← Finset.mul_sum, hcol]
      _ = r a * B.fpdim a * M := by
        simp only [M, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  rw [ha] at hb
  have hp := B.fpdim_pos a
  dsimp [M] at hb
  nlinarith

lemma totalFPdim_eq_twice_sign_kernel (r : ι → ℝ) (hr : ∀ i, r i = 1 ∨ r i = -1)
    (hm : ∀ i j k, 0 < B.N i j k → r k = r i * r j)
    (a : ι) (ha : r a = -1) :
    B.totalFPdim = 2 * ∑ i, if r i = 1 then B.fpdim i ^ 2 else 0 := by
  have hz := B.signed_fpdim_sum_zero r hr hm a ha
  have hs : (∑ i, r i * B.fpdim i ^ 2) =
      2 * (∑ i, if r i = 1 then B.fpdim i ^ 2 else 0) - B.totalFPdim := by
    simp only [totalFPdim, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rcases hr i with h | h
    · norm_num [h]
      ring
    · norm_num [h]
  linarith

end Paper18.FusionBasis

namespace Paper18.Category.SignKernel
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]
  (hχ : ∀ X : C, χ.hom.app X ≫ χ.hom.app X = 𝟙 X)

include hχ in
def signCharacter : Paper18.SignCharacter S.fusionBasis where
  val i := TensorAutomorphism.scalar χ (S.simpleObject i)
  val_mem i := by
    obtain ⟨g, hg⟩ := FixedBoundary.simple_homogeneous χ hχ (S.simpleObject i)
    rcases Paper18.ZMod.two_eq_zero_or_one g with rfl | rfl
    · left
      change χ.hom.app (S.simpleObject i) = (1 : ℂ) • 𝟙 _ at hg
      change simpleScalarEquiv (S.simpleObject i) (χ.hom.app (S.simpleObject i)) = 1
      rw [hg, simpleScalarEquiv_smul_id]
    · right
      change χ.hom.app (S.simpleObject i) = (-1 : ℂ) • 𝟙 _ at hg
      change simpleScalarEquiv (S.simpleObject i) (χ.hom.app (S.simpleObject i)) = -1
      rw [hg, simpleScalarEquiv_smul_id]
  val_one := TensorAutomorphism.scalar_unitLabel χ S
  val_dual i := TensorAutomorphism.scalar_dualLabel χ S i
  val_tensor i j k h := TensorAutomorphism.scalar_fusion χ S i j k h

def realSign (i : ι) : ℝ := ((signCharacter S χ hχ).val i).re

lemma realSign_mem (i : ι) : realSign S χ hχ i = 1 ∨ realSign S χ hχ i = -1 := by
  rcases (signCharacter S χ hχ).val_mem i with h | h <;>
    simp [realSign, h]

lemma realSign_tensor (i j k : ι) (h : 0 < S.fusionBasis.N i j k) :
    realSign S χ hχ k = realSign S χ hχ i * realSign S χ hχ j := by
  have ht := congrArg Complex.re ((signCharacter S χ hχ).val_tensor i j k h)
  rcases (signCharacter S χ hχ).val_mem i with hi | hi <;>
    rcases (signCharacter S χ hχ).val_mem j with hj | hj <;>
      simpa [realSign, hi, hj] using ht

lemma realSign_eq_one_iff (i : ι) : realSign S χ hχ i = 1 ↔ positiveProperty χ (S.simpleObject i) := by
  rw [mem_positive]
  have hs := TensorAutomorphism.scalar_spec χ (S.simpleObject i)
  rcases (signCharacter S χ hχ).val_mem i with hp | hn
  · change TensorAutomorphism.scalar χ (S.simpleObject i) = 1 at hp
    rw [hp, one_smul] at hs
    simp [realSign, hp, signCharacter, hs.symm]
  · change TensorAutomorphism.scalar χ (S.simpleObject i) = -1 at hn
    have hne : χ.hom.app (S.simpleObject i) ≠ (𝟙 (S.simpleObject i) : S.simpleObject i ⟶ S.simpleObject i) := by
      intro he
      have hsc : TensorAutomorphism.scalar χ (S.simpleObject i) = 1 := by
        unfold TensorAutomorphism.scalar
        rw [he]
        simpa using simpleScalarEquiv_smul_id (S.simpleObject i) (1 : ℂ)
      rw [hn] at hsc
      norm_num at hsc
    norm_num [realSign, signCharacter, hn, hne]

include hχ in
/-- Any actual negative simple forces the actual positive full fusion
subcategory to have half the ambient total FP dimension. -/
theorem supportFPdim_indexTwo (a : ι) (ha : χ.hom.app (S.simpleObject a) = -𝟙 _) :
    S.fusionBasis.totalFPdim = 2 * S.supportFPdim (positiveProperty χ) := by
  have hs : TensorAutomorphism.scalar χ (S.simpleObject a) = -1 := by
    unfold TensorAutomorphism.scalar
    rw [ha]
    simpa using simpleScalarEquiv_smul_id (S.simpleObject a) (-1 : ℂ)
  have hneg : realSign S χ hχ a = -1 := by simp [realSign, signCharacter, hs]
  have h := S.fusionBasis.totalFPdim_eq_twice_sign_kernel
    (realSign S χ hχ) (realSign_mem S χ hχ) (realSign_tensor S χ hχ) a hneg
  simpa only [FiniteSemisimpleSkeleton.supportFPdim, realSign_eq_one_iff] using h

include hχ in
/-- Nontriviality on an actual object is witnessed by a negative simple
in its actual chosen decomposition. -/
lemma exists_negative_label (X : C) (hX : χ.hom.app X ≠ 𝟙 X) :
    ∃ a : Fin (S.length X), χ.hom.app (S.simpleObject (S.label X a)) = -𝟙 _ := by
  have hn : ¬ ∀ a : Fin (S.length X), positiveProperty χ (S.simpleObject (S.label X a)) := by
    intro h
    exact hX ((mem_positive χ X).mp
      ((S.property_iff_labels (positiveProperty χ) X).mpr h))
  obtain ⟨a, ha⟩ := not_forall.mp hn
  refine ⟨a, ?_⟩
  rcases (signCharacter S χ hχ).val_mem (S.label X a) with hp | hm
  · change TensorAutomorphism.scalar χ (S.simpleObject (S.label X a)) = 1 at hp
    exfalso
    apply ha
    rw [mem_positive, ← TensorAutomorphism.scalar_spec, hp, one_smul]
  · change TensorAutomorphism.scalar χ (S.simpleObject (S.label X a)) = -1 at hm
    rw [← TensorAutomorphism.scalar_spec, hm, neg_one_smul]
    rfl

include hχ in
theorem supportFPdim_indexTwo_of_nontrivial (X : C) (hX : χ.hom.app X ≠ 𝟙 X) :
    S.fusionBasis.totalFPdim = 2 * S.supportFPdim (positiveProperty χ) := by
  obtain ⟨a, ha⟩ := exists_negative_label S χ hχ X hX
  exact supportFPdim_indexTwo S χ hχ (S.label X a) ha

/-- The total dimension is the intrinsic dimension of the actual inherited
positive fusion category, with its actual kernels and duals. -/
def positiveTotalFPdim : ℝ :=
  letI := hasKernels χ S
  letI := rightRigid χ S
  letI := simpleUnit χ S
  (skeleton χ S).fusionBasis.totalFPdim

lemma positiveTotalFPdim_eq_support :
    positiveTotalFPdim S χ = S.supportFPdim (positiveProperty χ) :=
  S.fullSubcategory_totalFPdim_eq (positiveProperty χ)

include hχ in
theorem totalFPdim_indexTwo_of_nontrivial (X : C) (hX : χ.hom.app X ≠ 𝟙 X) :
    S.fusionBasis.totalFPdim = 2 * positiveTotalFPdim S χ := by
  rw [positiveTotalFPdim_eq_support]
  exact supportFPdim_indexTwo_of_nontrivial S χ hχ X hX

end Paper18.Category.SignKernel
