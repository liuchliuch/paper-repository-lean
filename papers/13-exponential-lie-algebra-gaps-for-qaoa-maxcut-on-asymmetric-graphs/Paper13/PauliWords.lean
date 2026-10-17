import Paper13.MixerParity
import Mathlib.LinearAlgebra.LinearIndependent.Defs
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators

/-- Codes I,X,Y,Z. The XOR of codes gives multiplication modulo its scalar phase. -/
def pauliLetter (a : Fin 4) : Op1 := match a.val with
  | 0 => 1 | 1 => pauliX | 2 => pauliY | _ => pauliZ

def pauliXor (a b : Fin 4) : Fin 4 := match a.val with
  | 0 => b
  | 1 => match b.val with | 0 => 1 | 1 => 0 | 2 => 3 | _ => 2
  | 2 => match b.val with | 0 => 2 | 1 => 3 | 2 => 0 | _ => 1
  | _ => match b.val with | 0 => 3 | 1 => 2 | 2 => 1 | _ => 0

def pauliPhase (a b : Fin 4) : ℂ :=
  if a.val=0 ∨ b.val=0 ∨ a.val=b.val then 1 else
    if (a.val=1 ∧ b.val=2) ∨ (a.val=2 ∧ b.val=3) ∨ (a.val=3 ∧ b.val=1) then Complex.I else -Complex.I

lemma pauliLetter_mul (a b : Fin 4) : pauliLetter a*pauliLetter b=pauliPhase a b • pauliLetter (pauliXor a b) := by
  fin_cases a <;> fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauliLetter,pauliPhase,pauliXor,pauliX,pauliY,pauliZ,Matrix.mul_apply,Fin.sum_univ_two]

lemma pauliLetter_hermitian (a : Fin 4) : (pauliLetter a)ᴴ=pauliLetter a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauliLetter,pauliX,pauliY,pauliZ,Matrix.conjTranspose_apply]

lemma pauliLetter_trace_product (a b : Fin 4) : Matrix.trace (pauliLetter a*pauliLetter b) = if a=b then 2 else 0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [pauliLetter,pauliX,pauliY,pauliZ,Matrix.trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_two]

def pauliWord {n : ℕ} (w : Fin n → Fin 4) : Op n := tensorMatrix (fun v => pauliLetter (w v))
def skewPauliWord {n : ℕ} (w : Fin n → Fin 4) : Op n := Complex.I • pauliWord w

def wordXor {n : ℕ} (w z : Fin n → Fin 4) : Fin n → Fin 4 := fun v => pauliXor (w v) (z v)
def wordPhase {n : ℕ} (w z : Fin n → Fin 4) : ℂ := ∏ v, pauliPhase (w v) (z v)

lemma pauliWord_mul {n : ℕ} (w z : Fin n → Fin 4) : pauliWord w*pauliWord z=wordPhase w z • pauliWord (wordXor w z) := by
  simp only [pauliWord,wordPhase,wordXor,tensorMatrix_mul,pauliLetter_mul,tensorMatrix_smul]

lemma pauliWord_hermitian {n : ℕ} (w : Fin n → Fin 4) : (pauliWord w)ᴴ=pauliWord w := by
  simp only [pauliWord,tensorMatrix_conjTranspose,pauliLetter_hermitian]

lemma skewPauliWord_skew {n : ℕ} (w : Fin n → Fin 4) : (skewPauliWord w)ᴴ = -skewPauliWord w := by
  simp [skewPauliWord,Matrix.conjTranspose_smul,pauliWord_hermitian]

lemma pauliWord_trace_product {n : ℕ} (w z : Fin n → Fin 4) :
    Matrix.trace (pauliWord w*pauliWord z)=if w=z then (2^n : ℂ) else 0 := by
  simp only [pauliWord,tensorMatrix_mul,tensorMatrix_trace,pauliLetter_trace_product]
  by_cases h : w=z
  · subst z; simp
  · rw [if_neg h]
    obtain ⟨v,hv⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    exact if_neg hv

/-- Real coefficient extraction separates all skew Pauli words. -/
def pauliCoefficient {n : ℕ} (w : Fin n → Fin 4) : Op n →ₗ[ℝ] ℝ where
  toFun A := (Matrix.trace (pauliWord w*A)/((2^n : ℂ)*Complex.I)).re
  map_add' A B := by simp [mul_add,Matrix.trace_add,add_div]
  map_smul' r A := by simp [Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul,mul_div_assoc]

lemma pauliCoefficient_word {n : ℕ} (w z : Fin n → Fin 4) :
    pauliCoefficient w (skewPauliWord z)=if w=z then 1 else 0 := by
  change (Matrix.trace (pauliWord w*(Complex.I • pauliWord z))/((2^n : ℂ)*Complex.I)).re = _
  rw [Matrix.mul_smul,Matrix.trace_smul,pauliWord_trace_product]
  by_cases h : w=z
  · rw [if_pos h,if_pos h]
    simp only [smul_eq_mul]
    rw [mul_comm Complex.I,div_self (mul_ne_zero (pow_ne_zero _ (by norm_num)) Complex.I_ne_zero)]
    rfl
  · simp [h]

/-- All 4^n skew Pauli words are linearly independent over the actual real scalar field. -/
theorem skewPauliWords_independent (n : ℕ) : LinearIndependent ℝ (skewPauliWord (n := n)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc w
  have h := congrArg (pauliCoefficient w) hc
  simp only [map_sum,map_smul,pauliCoefficient_word,map_zero,smul_eq_mul] at h
  simpa using h

/-- Their span is the entire real skew-Hermitian space, by equality of finite dimensions. -/
theorem skewPauliWords_span (n : ℕ) :
    Submodule.span ℝ (Set.range (skewPauliWord (n := n))) = SkewHermOp n := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro A ⟨w,rfl⟩
    exact skewPauliWord_skew w
  · rw [finrank_span_eq_card (skewPauliWords_independent n),skewHermOp_finrank]
    simp [Fintype.card_fun,pow_mul,show (4 : ℕ)=2^2 by norm_num]
end Paper13
