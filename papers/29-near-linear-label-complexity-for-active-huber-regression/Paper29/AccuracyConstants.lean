import Paper29.TwoBatchProbability

noncomputable section
namespace Paper29.ProcessTools

def failureProbability : ℝ := 1/1000

def pilotC₀ : ℝ := pilotConstant failureProbability

def mainAccuracy (ε : ℝ) : ℝ := (2*ε+ε^2)/(2*pilotC₀)

theorem pilotC₀_large : 9 ≤ pilotC₀ := by
  have hspos : 0 < Real.sqrt ((1-1/8)*failureProbability) := Real.sqrt_pos.2 (by
    norm_num [failureProbability])
  have hs : Real.sqrt ((1-1/8)*failureProbability) ≤ 1 := Real.sqrt_le_one.mpr (by
    norm_num [failureProbability])
  have hfrac : 2 ≤ 2/Real.sqrt ((1-1/8)*failureProbability) := (le_div_iff₀ hspos).2 (by linarith)
  unfold pilotC₀ pilotConstant
  nlinarith

theorem mainAccuracy_spec {ε : ℝ} (hε : 0 < ε) (hεhi : ε < 1/2) :
    0 < mainAccuracy ε ∧ mainAccuracy ε < 1/2 ∧
      ε/pilotC₀ ≤ mainAccuracy ε ∧
      1/(mainAccuracy ε)^2 ≤ pilotC₀^2/ε^2 := by
  have hC : 0 < pilotC₀ := lt_of_lt_of_le (by norm_num : (0:ℝ)<9) pilotC₀_large
  have hη : 0 < mainAccuracy ε := by unfold mainAccuracy; positivity
  have hεC : ε ≤ pilotC₀ * mainAccuracy ε := by
    unfold mainAccuracy
    have he : pilotC₀ * ((2*ε+ε^2)/(2*pilotC₀)) = ε+ε^2/2 := by field_simp
    rw [he]
    nlinarith [sq_nonneg ε]
  refine ⟨hη, ?_, (div_le_iff₀ hC).2 (by simpa only [mul_comm] using hεC), ?_⟩
  · unfold mainAccuracy
    apply (div_lt_iff₀ (mul_pos (by norm_num) hC)).2
    have hs : ε^2 < 1/4 := by nlinarith [sq_nonneg (ε-1/2)]
    nlinarith [pilotC₀_large]
  · apply (div_le_div_iff₀ (sq_pos_of_pos hη) (sq_pos_of_pos hε)).2
    have hh := (sq_le_sq₀ hε.le (mul_nonneg hC.le hη.le)).2 hεC
    nlinarith

theorem overall_success_probability : (99/100:ℝ) ≤ 1-2*failureProbability-failureProbability := by
  norm_num [failureProbability]

end Paper29.ProcessTools
