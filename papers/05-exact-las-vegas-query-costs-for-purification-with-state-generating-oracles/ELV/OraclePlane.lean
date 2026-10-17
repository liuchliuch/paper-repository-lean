import ELV.OracleReflection
import ELV.PublicLine

/-! The unknown invariant plane of the pulled-back reflection, derived for
every full unitary completion. No gate depends on its second basis vector. -/
noncomputable section
namespace ELV.Model.Oracle
open ELV.Line
variable {n : ℕ} [NeZero n]

lemma matrixOff_sq (O : Oracle n) : matrixOff O.p ^ 2 = 4*O.p*(1-O.p) := by
  rw [matrixOff,mul_pow,Real.sq_sqrt (mul_nonneg O.p_nonneg (sub_nonneg.mpr O.p_le_one))]
  ring

lemma mean_off_identity (O : Oracle n) : 1-matrixMean O.p ^ 2 = matrixOff O.p ^ 2 := by
  rw [matrixOff_sq,matrixMean]
  ring

lemma matrixOff_pos (O : Oracle n) (hp0 : 0 < O.p) (hp1 : O.p < 1) : 0 < matrixOff O.p := by
  unfold matrixOff
  exact mul_pos (by norm_num) (Real.sqrt_pos.mpr (mul_pos hp0 (sub_pos.mpr hp1)))

/-- The completion-dependent second basis vector, used only in the proof and catalyst. -/
def tangent (O : Oracle n) : Mspace n :=
  ((matrixOff O.p)⁻¹ : ℂ) •
    (O.pulledReflection (knownInput n) - (matrixMean O.p : ℂ) • knownInput n)

lemma known_inner_self : inner ℂ (knownInput n) (knownInput n) = 1 := by
  simp [inner_self_eq_norm_sq_to_K,knownInput_norm]

lemma tangent_orthogonal (O : Oracle n) : inner ℂ (knownInput n) O.tangent = 0 := by
  rw [tangent,inner_smul_right,inner_sub_right,inner_smul_right,
    pulledReflection_expectation,known_inner_self]
  simp [matrixMean]

lemma reflected_inner_known (O : Oracle n) :
    inner ℂ (O.pulledReflection (knownInput n)) (knownInput n) = (matrixMean O.p : ℂ) := by
  rw [← inner_conj_symm,pulledReflection_expectation]
  exact Complex.conj_ofReal (matrixMean O.p)

lemma tangent_numerator_norm_sq (O : Oracle n) :
    ‖O.pulledReflection (knownInput n) - (matrixMean O.p : ℂ) • knownInput n‖ ^ 2 =
      1-matrixMean O.p ^ 2 := by
  rw [@norm_sub_sq ℂ]
  have hr : ‖O.pulledReflection (knownInput n)‖ = 1 := by rw [O.pulledReflection.norm_map,knownInput_norm]
  rw [hr,norm_smul,knownInput_norm,inner_smul_right,reflected_inner_known]
  simp [Complex.norm_real,Real.norm_eq_abs,sq_abs,Complex.mul_re]
  ring

lemma tangent_norm (O : Oracle n) (hp0 : 0 < O.p) (hp1 : O.p < 1) : ‖O.tangent‖ = 1 := by
  have hd := matrixOff_pos O hp0 hp1
  have hn : ‖O.tangent‖ ^ 2 = 1 := by
    rw [tangent,norm_smul,mul_pow,tangent_numerator_norm_sq,mean_off_identity]
    simp [Complex.norm_real,Real.norm_eq_abs,inv_pow,hd.ne']
  nlinarith [norm_nonneg O.tangent]

lemma reflected_known_plane (O : Oracle n) (hp0 : 0 < O.p) (hp1 : O.p < 1) :
    O.pulledReflection (knownInput n) =
      (matrixMean O.p : ℂ) • knownInput n + (matrixOff O.p : ℂ) • O.tangent := by
  have hd : (matrixOff O.p : ℂ) ≠ 0 := by exact_mod_cast (matrixOff_pos O hp0 hp1).ne'
  unfold tangent
  simp only [smul_smul]
  rw [mul_inv_cancel₀ hd,one_smul]
  module

lemma reflected_tangent_plane (O : Oracle n) (hp0 : 0 < O.p) (hp1 : O.p < 1) :
    O.pulledReflection O.tangent =
      (matrixOff O.p : ℂ) • knownInput n - (matrixMean O.p : ℂ) • O.tangent := by
  have hd : (matrixOff O.p : ℂ) ≠ 0 := by exact_mod_cast (matrixOff_pos O hp0 hp1).ne'
  calc
    _ = ((matrixOff O.p)⁻¹ : ℂ) • (knownInput n -
        (matrixMean O.p : ℂ) • O.pulledReflection (knownInput n)) := by
      rw [tangent,map_smul,map_sub,map_smul,pulledReflection_involutive]
    _ = ((matrixOff O.p)⁻¹ : ℂ) •
        (((1-matrixMean O.p ^ 2 : ℝ) : ℂ) • knownInput n -
          ((matrixMean O.p : ℂ)*(matrixOff O.p : ℂ)) • O.tangent) := by
      rw [reflected_known_plane O hp0 hp1]
      push_cast
      module
    _ = _ := by
      rw [mean_off_identity]
      push_cast
      simp only [smul_sub,smul_smul]
      field_simp

/-- At the probability endpoints the public vector is already an eigenvector. -/
lemma reflected_known_low_endpoint (O : Oracle n) (hp : O.p = 0) :
    O.pulledReflection (knownInput n) = knownInput n := by
  have hn : ‖O.pulledReflection (knownInput n)-knownInput n‖ ^ 2 = 0 := by
    rw [@norm_sub_sq ℂ,O.pulledReflection.norm_map,knownInput_norm,reflected_inner_known]
    norm_num [matrixMean,hp]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))

lemma reflected_known_high_endpoint (O : Oracle n) (hp : O.p = 1) :
    O.pulledReflection (knownInput n) = -knownInput n := by
  have hn : ‖O.pulledReflection (knownInput n)+knownInput n‖ ^ 2 = 0 := by
    rw [@norm_add_sq ℂ,O.pulledReflection.norm_map,knownInput_norm,reflected_inner_known]
    norm_num [matrixMean,hp]
  exact eq_neg_of_add_eq_zero_left (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))

end ELV.Model.Oracle
