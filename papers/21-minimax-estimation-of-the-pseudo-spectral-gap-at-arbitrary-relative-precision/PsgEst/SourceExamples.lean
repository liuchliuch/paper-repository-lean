import PsgEst.GapsOfPowers

/-!
# Endpoint estimator and the shift-register counterexample

These are the substantive examples in source paragraphs S1.p10 and S2.p9.
-/

open Matrix BigOperators Real Finset Classical

namespace PsgEst

/-- Above the endpoint threshold, the constant output `1-ε` has relative error
at most `ε` simultaneously throughout `[g,1]`, with no observations. -/
theorem constant_endpoint_relative_accuracy {ε g γ : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hg : (1 - ε) / (1 + ε) ≤ g) (hγ : g ≤ γ) (hγ1 : γ ≤ 1) :
    |(1 - ε) - γ| ≤ ε * γ := by
  have hden : 0 < 1 + ε := by linarith
  have hupper := (div_le_iff₀ hden).mp (hg.trans hγ)
  have hlower := mul_le_mul_of_nonneg_left hγ1 (sub_nonneg.mpr hε1)
  rw [abs_le]
  constructor <;> nlinarith

/-- The four-state shift-register transition matrix from S2.p9. -/
noncomputable def shiftRegisterP : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(1 / 2 : ℝ), 1 / 2, 0, 0;
     0, 0, 1 / 2, 1 / 2;
     1 / 2, 1 / 2, 0, 0;
     0, 0, 1 / 2, 1 / 2]

/-- The uniform stationary projection. -/
noncomputable def shiftRegisterPi : Matrix (Fin 4) (Fin 4) ℝ := fun _ _ => 1 / 4

noncomputable def shiftRegisterStoch : Stoch 4 where
  P := shiftRegisterP
  nonneg := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [shiftRegisterP]
  row_stoch := by
    intro i
    fin_cases i <;> norm_num [shiftRegisterP, Fin.sum_univ_succ]

noncomputable def shiftRegisterStationary : Stationary shiftRegisterStoch where
  mu := fun _ => 1 / 4
  pos := by intro i; norm_num
  sum_one := by norm_num [Fin.sum_univ_succ]
  station := by
    intro j
    fin_cases j <;> norm_num [shiftRegisterStoch, shiftRegisterP, Fin.sum_univ_succ]

/-- The example is doubly stochastic. -/
theorem shiftRegister_column_stoch (j : Fin 4) : ∑ i, shiftRegisterP i j = 1 := by
  fin_cases j <;> norm_num [shiftRegisterP, Fin.sum_univ_succ]

/-- Two shift operations erase both original bits. -/
theorem shiftRegister_square : shiftRegisterP ^ 2 = shiftRegisterPi := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_two, Matrix.mul_apply, shiftRegisterP, shiftRegisterPi, Fin.sum_univ_succ]

lemma shiftRegister_half_rpow : (1 / 4 : ℝ) ^ (1 / 2 : ℝ) = 1 / 2 := by
  rw [← Real.sqrt_eq_rpow]
  norm_num

lemma shiftRegister_inv_half_rpow : (1 / 4 : ℝ) ^ (-(1 / 2 : ℝ)) = 2 := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 4), shiftRegister_half_rpow]
  norm_num

/-- Uniform stationarity leaves the similarity transform unchanged. -/
theorem shiftRegister_Lk (n : ℕ) :
    Lk shiftRegisterStoch shiftRegisterStationary n = shiftRegisterP ^ n := by
  ext i j
  simp only [Lk, simil, Matrix.mul_diagonal, Matrix.diagonal_mul,
    shiftRegisterStationary, shiftRegisterStoch,
    shiftRegister_half_rpow, shiftRegister_inv_half_rpow]
  ring

private noncomputable def shiftFixed : Fin 4 → ℝ := fun _ => 1 / 2
private noncomputable def shiftWitness : Fin 4 → ℝ := ![1 / 2, 1 / 2, -1 / 2, -1 / 2]

private lemma shiftFixed_unit : ∑ i, shiftFixed i * shiftFixed i = 1 := by
  norm_num [shiftFixed, Fin.sum_univ_succ]

private lemma shiftFixed_P : shiftRegisterP *ᵥ shiftFixed = shiftFixed := by
  ext i
  fin_cases i <;> norm_num [shiftRegisterP, shiftFixed, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private lemma shiftFixed_PT : shiftRegisterP.transpose *ᵥ shiftFixed = shiftFixed := by
  ext i
  fin_cases i <;> norm_num [shiftRegisterP, shiftFixed, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Fin.sum_univ_succ]

private lemma shiftP_contraction (x : Fin 4 → ℝ) :
    ∑ i, (shiftRegisterP *ᵥ x) i ^ 2 ≤ ∑ i, x i ^ 2 := by
  have h := Lk_contraction shiftRegisterStoch shiftRegisterStationary 1 x
  simpa [shiftRegister_Lk] using h

/-- The second singular value is one, although the chain mixes after two steps. -/
theorem shiftRegister_sigma2 : sigma2 shiftRegisterP = 1 := by
  have hm := sigma2_mem_of_contraction shiftRegisterP shiftP_contraction
  have h := (sigma2_rayleigh_fixed shiftRegisterP shiftFixed (by norm_num)
    shiftFixed_unit shiftFixed_P shiftFixed_PT shiftP_contraction).1 shiftWitness
      (by norm_num [shiftWitness, Fin.sum_univ_succ])
      (by norm_num [shiftWitness, shiftFixed, Fin.sum_univ_succ])
  have hw : (∑ i, (shiftRegisterP *ᵥ shiftWitness) i ^ 2) = 1 := by
    norm_num [shiftRegisterP, shiftWitness, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [hw] at h
  nlinarith

private lemma shiftFixed_Pi : shiftRegisterPi *ᵥ shiftFixed = shiftFixed := by
  ext i
  norm_num [shiftRegisterPi, shiftFixed, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private lemma shiftFixed_PiT : shiftRegisterPi.transpose *ᵥ shiftFixed = shiftFixed := by
  ext i
  norm_num [shiftRegisterPi, shiftFixed, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Fin.sum_univ_succ]

private lemma shiftPi_contraction (x : Fin 4 → ℝ) :
    ∑ i, (shiftRegisterPi *ᵥ x) i ^ 2 ≤ ∑ i, x i ^ 2 := by
  have h := Lk_contraction shiftRegisterStoch shiftRegisterStationary 2 x
  simpa [shiftRegister_Lk, shiftRegister_square] using h

/-- The uniform projection has no singular action orthogonal to constants. -/
theorem shiftRegisterPi_sigma2 : sigma2 shiftRegisterPi = 0 := by
  obtain ⟨x, hx, horth, hnorm⟩ :=
    (sigma2_rayleigh_fixed shiftRegisterPi shiftFixed (by norm_num)
      shiftFixed_unit shiftFixed_Pi shiftFixed_PiT shiftPi_contraction).2
  have hxsum : ∑ i, x i = 0 := by
    have h : (∑ i, x i) * (1 / 2 : ℝ) = 0 := by
      simpa only [shiftFixed, Finset.sum_mul] using horth
    linarith
  have hzero : shiftRegisterPi *ᵥ x = 0 := by
    ext i
    simp [shiftRegisterPi, Matrix.mulVec, dotProduct, ← Finset.mul_sum, hxsum]
  rw [hzero] at hnorm
  norm_num at hnorm
  nlinarith

@[simp] theorem shiftRegister_aK_one :
    aK shiftRegisterStoch shiftRegisterStationary 1 = 0 := by
  simp [aK, aOf, shiftRegister_Lk, shiftRegister_sigma2]

@[simp] theorem shiftRegister_aK_two :
    aK shiftRegisterStoch shiftRegisterStationary 2 = 1 := by
  simp [aK, aOf, shiftRegister_Lk, shiftRegister_square, shiftRegisterPi_sigma2]

/-- The first nonzero lag deficit is attained at lag two, giving `γ_ps(P)=1/2`. -/
theorem shiftRegister_gammaPS :
    gammaPS shiftRegisterStoch shiftRegisterStationary = 1 / 2 := by
  rw [gammaPS_eq_gapGamma]
  refine le_antisymm ?_ ?_
  · apply ciSup_le
    intro k
    by_cases hk : 0 < k
    · rw [if_pos hk]
      by_cases hk1 : k = 1
      · subst k
        norm_num
      · have hk2 : 2 ≤ k := by omega
        have hkR : (0 : ℝ) < k := by exact_mod_cast hk
        have hk2R : (2 : ℝ) ≤ k := by exact_mod_cast hk2
        rw [div_le_iff₀ hkR]
        have hm := (aK_mem shiftRegisterStoch shiftRegisterStationary k).2
        linarith
    · simp [hk]
  · have h := le_gapGamma (aK shiftRegisterStoch shiftRegisterStationary)
      (k := 2) (by norm_num) (fun t => (aK_mem _ _ t).2)
    simpa using h

/-- The squared chain has pseudo-spectral gap one. -/
theorem shiftRegister_square_gammaPS :
    gammaPS (shiftRegisterStoch.pow 2)
      (stationaryPow shiftRegisterStoch shiftRegisterStationary 2) = 1 := by
  rw [gammaPS_eq_gapGamma]
  refine le_antisymm (gapGamma_le_one _ (fun t => (aK_mem _ _ t).2)) ?_
  have h := le_gapGamma
    (aK (shiftRegisterStoch.pow 2) (stationaryPow shiftRegisterStoch shiftRegisterStationary 2))
    (k := 1) (by norm_num) (fun t => (aK_mem _ _ t).2)
  rw [aK_pow] at h
  simpa using h

/-- The reversible scalar power formula would give `3/4` instead of the actual `1`. -/
theorem shiftRegister_scalar_formula :
    1 - (1 - gammaPS shiftRegisterStoch shiftRegisterStationary) ^ 2 = (3 / 4 : ℝ) := by
  rw [shiftRegister_gammaPS]
  norm_num

/-- Hence the scalar power identity fails for this explicitly specified chain. -/
theorem shiftRegister_power_identity_fails :
    gammaPS (shiftRegisterStoch.pow 2)
      (stationaryPow shiftRegisterStoch shiftRegisterStationary 2) ≠
      1 - (1 - gammaPS shiftRegisterStoch shiftRegisterStationary) ^ 2 := by
  rw [shiftRegister_square_gammaPS, shiftRegister_scalar_formula]
  norm_num

/-- The counterexample satisfies the finite ergodicity package used throughout the paper. -/
noncomputable def shiftRegisterErgodic : Ergodic 4 where
  S := shiftRegisterStoch
  st := shiftRegisterStationary
  gap_pos := by rw [shiftRegister_gammaPS]; norm_num
  gap_le_one := by rw [shiftRegister_gammaPS]; norm_num

end PsgEst
