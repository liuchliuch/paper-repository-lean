import Paper13.PauliSupport
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma pauliX_entry (x y : Fin 2) : pauliX x y=if y=1-x then 1 else 0 := by
  fin_cases x <;> fin_cases y <;> norm_num [pauliX]
lemma pauliWord_identity (n : ℕ) : pauliWord (fun _ : Fin n => 0)=1 := by
  exact tensorMatrix_one
lemma pauliWord_globalX (n : ℕ) : pauliWord (fun _ : Fin n => 1)=bitFlip n := by
  ext x y
  change (∏ v : Fin n, pauliX (x v) (y v))=if y=flipState x then 1 else 0
  simp only [pauliX_entry]
  by_cases h : y=flipState x
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro v hv
    have hv : y v=1-x v := congrFun h v
    simp [hv]
  · rw [if_neg h]
    obtain ⟨v,hv⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simpa only [flipState] using if_neg hv

lemma pauliLetter_X_conjugation (a : Fin 4) :
    pauliX*pauliLetter a*pauliX=(pauliGrade a : ℂ) • pauliLetter a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauliLetter,pauliGrade,pauliX,pauliY,pauliZ,Matrix.mul_apply,Fin.sum_univ_two]

lemma pauliWord_parity_conjugation {n : ℕ} (w : Fin n → Fin 4) :
    bitFlip n * pauliWord w * bitFlip n=(wordGrade w : ℂ) • pauliWord w := by
  rw [←pauliWord_globalX,pauliWord,pauliWord,tensorMatrix_mul,tensorMatrix_mul]
  simp only [show pauliLetter (1 : Fin 4)=pauliX from rfl,pauliLetter_X_conjugation,tensorMatrix_smul,wordGrade,Int.cast_prod]

lemma pauliWord_odd_anticomm {n : ℕ} (w : Fin n → Fin 4) (hw : wordGrade w= -1) :
    pauliWord w*bitFlip n= -(bitFlip n*pauliWord w) := by
  have h := congrArg (fun A : Op n => bitFlip n*A) (pauliWord_parity_conjugation w)
  rw [hw] at h
  simp only [Int.cast_neg,Int.cast_one,neg_one_smul,mul_neg] at h
  simpa only [←mul_assoc,bitFlip_sq_one,one_mul] using h

lemma pauliCoefficient_odd_zero {n : ℕ} (w : Fin n → Fin 4) (hw : ¬EvenPauli w)
    (A : Op n) (hA : A*bitFlip n=bitFlip n*A) : pauliCoefficient w A=0 := by
  have hg : wordGrade w= -1 := (mul_self_eq_one_iff.mp (wordGrade_sq w)).resolve_left hw
  have ht : Matrix.trace (pauliWord w*A)=0 := by
    apply trace_zero_of_anticomm _ (bitFlip n) (bitFlip_sq_one n)
    rw [mul_assoc,hA,←mul_assoc,pauliWord_odd_anticomm w hg,neg_mul,mul_assoc]
  simp [pauliCoefficient,ht]

lemma pauliCoefficient_identity_zero {n : ℕ} (A : Op n) (hA : Matrix.trace A=0) :
    pauliCoefficient (fun _ : Fin n => 0) A=0 := by
  simp [pauliCoefficient,pauliWord_identity,hA]
lemma pauliCoefficient_globalX_zero {n : ℕ} (A : Op n) (hA : Matrix.trace (A*bitFlip n)=0) :
    pauliCoefficient (fun _ : Fin n => 1) A=0 := by
  change (Matrix.trace (pauliWord (fun _ : Fin n => 1)*A)/((2^n : ℂ)*Complex.I)).re=0
  rw [pauliWord_globalX,Matrix.trace_mul_comm,hA]
  simp

lemma pauli_expansion {n : ℕ} (A : Op n) (hA : Aᴴ= -A) :
    A=∑ w : Fin n → Fin 4, (pauliCoefficient w A) • skewPauliWord w := by
  have hs : A ∈ Submodule.span ℝ (Set.range (skewPauliWord (n := n))) := by
    rw [skewPauliWords_span]; exact hA
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hs
  have hc' : ∀ w, c w=pauliCoefficient w A := by
    intro w
    have h := congrArg (pauliCoefficient w) hc
    simpa only [map_sum,map_smul,pauliCoefficient_word,smul_eq_mul,
      mul_ite,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true,mul_one,mul_zero] using h
  simpa only [hc'] using hc.symm

/-- The actual skew-Hermitian parity commutant with both traces zero has precisely the admissible support. -/
theorem mem_admissible_span {n : ℕ} (A : Op n) (hsk : Aᴴ= -A)
    (hc : A*bitFlip n=bitFlip n*A) (ht : Matrix.trace A=0) (hf : Matrix.trace (A*bitFlip n)=0) :
    A ∈ Submodule.span ℝ (Set.range (fun w : {w : Fin n → Fin 4 // AdmissiblePauli w} => skewPauliWord w.val)) := by
  rw [pauli_expansion A hsk]
  apply Submodule.sum_mem
  intro w hw
  by_cases ha : AdmissiblePauli w
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨w,ha⟩,rfl⟩)
  · have hz : pauliCoefficient w A=0 := by
      by_cases he : EvenPauli w
      · by_cases h0 : w=fun _ => 0
        · subst w; exact pauliCoefficient_identity_zero A ht
        by_cases h1 : w=fun _ => 1
        · subst w; exact pauliCoefficient_globalX_zero A hf
        exact False.elim (ha ⟨he,h0,h1⟩)
      · exact pauliCoefficient_odd_zero w he A hc
    rw [hz,zero_smul]
    exact Submodule.zero_mem _
end Paper13
