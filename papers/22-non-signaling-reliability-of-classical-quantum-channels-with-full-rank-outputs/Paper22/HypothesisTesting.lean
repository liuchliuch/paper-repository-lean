import Paper22.Divergences
import Paper22.Programs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

/-! Matrix testing risk and the Petz trace bound needed for exponent achievability. -/
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace Paper22
local instance testingMatrixCStarAlgebra (d : ℕ) : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) where
variable {d : ℕ}

/-- The quantum binary-testing optimum, as the trace of the noncommutative minimum. -/
def testingRisk (A B : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (A - (A-B)⁺).trace.re

/-- Positive complementary powers multiply to the original positive matrix,
including when the matrix is singular. -/
theorem matrix_rpow_mul_complement {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : 0 ≤ A) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    CFC.rpow A α * CFC.rpow A (1-α) = A := by
  let a : NNReal := ⟨α, hα.1.le⟩
  let b : NNReal := ⟨1-α, by linarith [hα.2]⟩
  have ha : 0 < a := hα.1
  have hb : 0 < b := by change (0:ℝ)<1-α; linarith [hα.2]
  have hab : a+b=1 := by apply Subtype.ext; change α+(1-α)=1; ring
  have heqa : CFC.nnrpow A a = CFC.rpow A α := CFC.nnrpow_eq_rpow ha
  have heqb : CFC.nnrpow A b = CFC.rpow A (1-α) := CFC.nnrpow_eq_rpow hb
  calc CFC.rpow A α * CFC.rpow A (1-α) = CFC.nnrpow A a * CFC.nnrpow A b := by
         rw [heqa, heqb]
       _ = CFC.nnrpow A (a+b) := (CFC.nnrpow_add ha hb).symm
       _ = A := by rw [hab]; exact CFC.nnrpow_one A hA

/-- The Audenaert--Petz testing bound for actual positive matrices.
This uses operator monotonicity of powers twice and positivity of the trace
pairing; no commutation assumption or hypothesis-testing oracle is introduced. -/
theorem testingRisk_le_petzTrace {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    testingRisk A B ≤ petzTrace α A B := by
  let C := B + (A-B)⁺
  have hAB : IsSelfAdjoint (A-B) := (IsSelfAdjoint.of_nonneg hA).sub (IsSelfAdjoint.of_nonneg hB)
  have hBC : B ≤ C := le_add_of_nonneg_right (CFC.posPart_nonneg _)
  have hAC : A ≤ C := by
    have h := CFC.le_posPart hAB
    have hh := add_le_add_left h B
    convert hh using 1 <;> abel
  have hC : 0 ≤ C := hB.trans hBC
  have ha : α ∈ Set.Icc 0 1 := ⟨hα.1.le, hα.2.le⟩
  have hb : 1-α ∈ Set.Icc 0 1 := by constructor <;> linarith [hα.1, hα.2]
  have hAp : CFC.rpow A α ≤ CFC.rpow C α := CFC.rpow_le_rpow ha hAC
  have hBp : CFC.rpow B α ≤ CFC.rpow C α := CFC.rpow_le_rpow ha hBC
  have hAm : CFC.rpow A (1-α) ≤ CFC.rpow C (1-α) := CFC.rpow_le_rpow hb hAC
  have hBm : CFC.rpow B (1-α) ≤ CFC.rpow C (1-α) := CFC.rpow_le_rpow hb hBC
  have hpowA : 0 ≤ CFC.rpow A α := CFC.rpow_nonneg (a := A) (y := α)
  have h1 := trace_mul_mono_re hpowA.posSemidef hAm
  rw [matrix_rpow_mul_complement hA hα] at h1
  have h2 := divergence_trace_mul_mono hAp (sub_nonneg.mpr hBm)
  have hpowB : 0 ≤ CFC.rpow B (1-α) := CFC.rpow_nonneg (a := B) (y := 1-α)
  have h3 := divergence_trace_mul_mono hBp hpowB
  rw [matrix_rpow_mul_complement hB hα] at h3
  have h4 : (CFC.rpow C α * CFC.rpow C (1-α)).trace.re = C.trace.re := by
    rw [matrix_rpow_mul_complement hC hα]
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at h2
  rw [h4] at h2
  have htraceC : C.trace.re = B.trace.re + ((A-B)⁺).trace.re := by
    simp only [C, Matrix.trace_add, Complex.add_re]
  unfold testingRisk petzTrace
  rw [Matrix.trace_sub, Complex.sub_re]
  linarith

/-- The test which accepts the positive spectrum of a Hermitian difference. -/
def positiveTest (D : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  cfc (fun t : ℝ => if 0 < t then (1 : ℝ) else 0) D

theorem positiveTest_isEffect (D : Matrix (Fin d) (Fin d) ℂ) :
    IsEffect (positiveTest D) := by
  constructor
  · apply cfc_nonneg
    intro t _
    split_ifs <;> norm_num
  · apply cfc_le_one
    intro t _
    split_ifs <;> norm_num

theorem mul_positiveTest {D : Matrix (Fin d) (Fin d) ℂ} (hD : IsSelfAdjoint D) :
    D * positiveTest D = D⁺ := by
  have hf : ContinuousOn (fun t : ℝ => if 0 < t then (1 : ℝ) else 0) (spectrum ℝ D) :=
    D.finite_real_spectrum.continuousOn _
  unfold positiveTest
  calc D * cfc (fun t : ℝ => if 0 < t then (1 : ℝ) else 0) D
      = cfc (id : ℝ → ℝ) D * cfc (fun t : ℝ => if 0 < t then (1 : ℝ) else 0) D := by
          rw [cfc_id ℝ D hD]
    _ = cfc (fun t : ℝ => t * (if 0 < t then (1 : ℝ) else 0)) D :=
      (cfc_mul _ _ D (hf := by fun_prop) (hg := by exact hf)).symm
    _ = D⁺ := by
      rw [CFC.posPart_def, cfcₙ_eq_cfc]
      apply cfc_congr
      intro t _
      dsimp only
      split_ifs with ht
      · simp [posPart_def, max_eq_left ht.le]
      · simp [posPart_def, max_eq_right (le_of_not_gt ht)]

/-- Error risk of a concrete binary test. -/
def testError (A B T : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (A * (1-T)).trace.re + (B*T).trace.re

theorem testError_eq_trace_sub (A B T : Matrix (Fin d) (Fin d) ℂ) :
    testError A B T = A.trace.re - ((A-B)*T).trace.re := by
  simp only [testError, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
    Matrix.trace_sub, Complex.sub_re]
  ring

/-- Helstrom's positive spectral test attains the trace expression. -/
theorem testError_positiveTest {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    testError A B (positiveTest (A-B)) = testingRisk A B := by
  rw [testError_eq_trace_sub,
    mul_positiveTest ((IsSelfAdjoint.of_nonneg hA).sub (IsSelfAdjoint.of_nonneg hB))]
  simp only [testingRisk, Matrix.trace_sub, Complex.sub_re]

/-- Every binary effect has risk at least the Helstrom trace expression. -/
theorem testingRisk_le_testError {A B T : Matrix (Fin d) (Fin d) ℂ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : IsEffect T) :
    testingRisk A B ≤ testError A B T := by
  have hD : IsSelfAdjoint (A-B) :=
    (IsSelfAdjoint.of_nonneg hA).sub (IsSelfAdjoint.of_nonneg hB)
  have h1 := divergence_trace_mul_mono (CFC.le_posPart hD) hT.1
  have h2 := trace_mul_mono_re (CFC.posPart_nonneg (A-B)).posSemidef hT.2
  rw [Matrix.mul_one] at h2
  rw [testError_eq_trace_sub]
  simp only [testingRisk, Matrix.trace_sub, Complex.sub_re]
  linarith

theorem testError_nonneg {A B T : Matrix (Fin d) (Fin d) ℂ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : IsEffect T) :
    0 ≤ testError A B T :=
  add_nonneg (trace_mul_nonneg_re hA.posSemidef (sub_nonneg.mpr hT.2).posSemidef)
    (trace_mul_nonneg_re hB.posSemidef hT.1.posSemidef)

theorem testingRisk_nonneg {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ testingRisk A B := by
  rw [← testError_positiveTest hA hB]
  exact testError_nonneg hA hB (positiveTest_isEffect _)

/-- A concrete effect realizes the Petz bound. -/
theorem exists_testError_le_petzTrace {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    ∃ T, IsEffect T ∧ testError A B T ≤ petzTrace α A B := by
  refine ⟨positiveTest (A-B), positiveTest_isEffect _, ?_⟩
  rw [testError_positiveTest hA hB]
  exact testingRisk_le_petzTrace hA hB hα

end Paper22
end
