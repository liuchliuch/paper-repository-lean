import Paper13.MatrixDimension
import Mathlib.Algebra.BigOperators.Ring.Finset
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators

/-- Tensor product of a finite family of local matrices, on the actual product basis. -/
def tensorMatrix {κ ι : Type*} [Fintype κ] (A : κ → Matrix ι ι ℂ) :
    Matrix (κ → ι) (κ → ι) ℂ := fun x y => ∏ v, A v (x v) (y v)

lemma tensorMatrix_mul {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    (A B : κ → Matrix ι ι ℂ) : tensorMatrix A * tensorMatrix B = tensorMatrix (fun v => A v * B v) := by
  ext x y
  simp only [Matrix.mul_apply, tensorMatrix, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun v z => A v (x v) z * B v z (y v))).symm

lemma tensorMatrix_one {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] :
    tensorMatrix (fun _ : κ => (1 : Matrix ι ι ℂ)) = 1 := by
  ext x y
  classical
  simp only [tensorMatrix, Matrix.one_apply]
  by_cases hxy : x = y
  · subst y; simp
  · rw [if_neg hxy]
    obtain ⟨v,hv⟩ := Function.ne_iff.mp hxy
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    exact if_neg hv

lemma tensorMatrix_trace {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    (A : κ → Matrix ι ι ℂ) : Matrix.trace (tensorMatrix A) = ∏ v, Matrix.trace (A v) := by
  simp only [Matrix.trace, Matrix.diag, tensorMatrix]
  exact (Fintype.prod_sum (fun v z => A v z z)).symm

lemma tensorMatrix_idem {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    (P : κ → Matrix ι ι ℂ) (hP : ∀ v, P v * P v = P v) : tensorMatrix P * tensorMatrix P = tensorMatrix P := by
  rw [tensorMatrix_mul]
  simp only [hP]

/-- Tensor-product ranks, proved from the actual matrices and their idempotence. -/
theorem tensorMatrix_finrank {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (P : κ → Matrix ι ι ℂ) (hP : ∀ v, P v * P v = P v) :
    Module.finrank ℂ (LinearMap.range (Matrix.toLin' (tensorMatrix P))) =
      ∏ v, Module.finrank ℂ (LinearMap.range (Matrix.toLin' (P v))) := by
  have ht := tensorMatrix_trace P
  rw [trace_eq_range_finrank _ (tensorMatrix_idem P hP)] at ht
  simp only [trace_eq_range_finrank _ (hP _)] at ht
  exact_mod_cast ht

/-- Each binary choice is the gadget projector or its complementary projector. -/
def binaryFactor {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ) (b : Bool) : Matrix ι ι ℂ :=
  if b then P else 1-P

lemma binaryFactor_idem {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ)
    (hP : P*P=P) (b : Bool) : binaryFactor P b * binaryFactor P b = binaryFactor P b := by
  cases b
  · simp only [binaryFactor, Bool.false_eq_true, ↓reduceIte]
    noncomm_ring [hP]
  · exact hP

/-- The complete family of joint binary projectors sums to the identity. -/
theorem binary_blocks_sum {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℂ) : (∑ s : κ → Bool, tensorMatrix (fun v => binaryFactor P (s v))) = 1 := by
  ext x y
  simp only [Matrix.sum_apply, tensorMatrix]
  rw [← Fintype.prod_sum (fun (v : κ) (b : Bool) => binaryFactor P b (x v) (y v))]
  have hf (v : κ) : (∑ b : Bool, binaryFactor P b (x v) (y v)) = (1 : Matrix ι ι ℂ) (x v) (y v) := by
    simp [binaryFactor, Fintype.sum_bool]
  simp only [hf]
  exact congrArg (fun M : Matrix (κ → ι) (κ → ι) ℂ => M x y) tensorMatrix_one

/-- The sum of squared joint ranks is the product of the local sum of squares.
This is the operator-level binomial amplification, not an assumed rank certificate. -/
theorem binary_blocks_sum_rank_sq {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ) (hP : P*P=P) :
    (∑ s : κ → Bool, (Module.finrank ℂ (LinearMap.range
      (Matrix.toLin' (tensorMatrix (fun v => binaryFactor P (s v))))))^2) =
    ((Module.finrank ℂ (LinearMap.range (Matrix.toLin' P)))^2 +
      (Module.finrank ℂ (LinearMap.range (Matrix.toLin' (1-P))))^2)^(Fintype.card κ) := by
  simp only [tensorMatrix_finrank _ (fun v => binaryFactor_idem P hP _)]
  simp only [← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun (_ : κ) (b : Bool) => (Module.finrank ℂ (LinearMap.range (Matrix.toLin' (binaryFactor P b))))^2)]
  simp [binaryFactor, Fintype.sum_bool, add_comm]
lemma tensorMatrix_conjTranspose {κ ι : Type*} [Fintype κ]
    (A : κ → Matrix ι ι ℂ) : (tensorMatrix A)ᴴ = tensorMatrix (fun v => (A v)ᴴ) := by
  ext x y
  simp [tensorMatrix, Matrix.conjTranspose_apply]

lemma binaryFactor_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℂ) (hP : P*P=P) (b c : Bool) (hbc : b ≠ c) :
    binaryFactor P b * binaryFactor P c = 0 := by
  cases b <;> cases c <;> simp_all [binaryFactor, sub_mul, mul_sub]

/-- Different binary sectors are orthogonal as actual matrix projectors. -/
theorem binary_blocks_orthogonal {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ) (hP : P*P=P)
    (s t : κ → Bool) (hst : s ≠ t) :
    tensorMatrix (fun v => binaryFactor P (s v)) *
      tensorMatrix (fun v => binaryFactor P (t v)) = 0 := by
  rw [tensorMatrix_mul]
  obtain ⟨v,hv⟩ := Function.ne_iff.mp hst
  ext x y
  change (∏ w, (binaryFactor P (s w) * binaryFactor P (t w)) (x w) (y w)) = 0
  apply Finset.prod_eq_zero (Finset.mem_univ v)
  rw [binaryFactor_orthogonal P hP _ _ hv]
  rfl

/-- Complementary projector rank, without an assumed rank formula. -/
theorem complement_projector_finrank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℂ) (hP : P*P=P) :
    Module.finrank ℂ (LinearMap.range (Matrix.toLin' (1-P))) =
      Fintype.card ι - Module.finrank ℂ (LinearMap.range (Matrix.toLin' P)) := by
  have hQ : (1-P)*(1-P)=1-P := by simp only [sub_mul,mul_sub,one_mul,mul_one,hP]; abel
  have hp := trace_eq_range_finrank P hP
  have hq := trace_eq_range_finrank (1-P) hQ
  have hsum : (Module.finrank ℂ (LinearMap.range (Matrix.toLin' P)) : ℂ) +
      (Module.finrank ℂ (LinearMap.range (Matrix.toLin' (1-P))) : ℂ) = (Fintype.card ι : ℂ) := by
    rw [← hp, ← hq, Matrix.trace_sub, Matrix.trace_one]
    ring
  have hn : Module.finrank ℂ (LinearMap.range (Matrix.toLin' P)) +
      Module.finrank ℂ (LinearMap.range (Matrix.toLin' (1-P))) = Fintype.card ι := by exact_mod_cast hsum
  omega
end Paper13

