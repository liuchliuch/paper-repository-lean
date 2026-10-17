import CalibrationDistance.ProtocolUniform
import CalibrationDistance.MomentsTails

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal

namespace CalibrationDistance.Protocol

/-- The conditional Bernoulli fluctuation has the sharp Hoeffding proxy `1/4`. -/
theorem bernoulli_centered_subgaussian {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    HasSubgaussianMGF (fun y : Bool => (if y then (1 : ℝ) else 0) - q)
      (1 / 4 : ℝ≥0) (bernoulliMeasure q) := by
  have hval : Measurable (fun y : Bool => if y then (1 : ℝ) else 0) := measurable_of_finite _
  have hmean : (∫ y : Bool, (if y then (1 : ℝ) else 0) ∂bernoulliMeasure q) = q := by
    rw [integral_bernoulliMeasure hq]
    simp
  have h := hasSubgaussianMGF_of_mem_Icc (μ := bernoulliMeasure q) hval.aemeasurable
    (Eventually.of_forall fun y => show (if y then (1 : ℝ) else 0) ∈ Icc (0 : ℝ) 1 by
      cases y <;> norm_num)
  norm_num [hmean] at h ⊢
  exact h

/-- At a fixed public history the forecast may have any probability law on `[0,1]`.
Independence in the simultaneous transition gives the paper's conditional mgf bound. -/
theorem simultaneous_step_subgaussian (μ : Measure Probability) [IsProbabilityMeasure μ]
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    HasSubgaussianMGF
      (fun r : Round => ((if r.2 then (1 : ℝ) else 0) - q) -
        ((r.1 : ℝ) - ∫ p : Probability, (p : ℝ) ∂μ))
      (1 / 2 : ℝ≥0) (μ.prod (bernoulliMeasure q)) := by
  let m : ℝ := ∫ p : Probability, (p : ℝ) ∂μ
  have hF : HasSubgaussianMGF (fun p : Probability => -((p : ℝ) - m))
      (1 / 4 : ℝ≥0) μ := by
    have h := hasSubgaussianMGF_of_mem_Icc (μ := μ)
      (measurable_subtype_coe.aemeasurable : AEMeasurable (fun p : Probability => (p : ℝ)) μ)
      (Eventually.of_forall fun p : Probability => p.property)
    have h' : HasSubgaussianMGF (fun p : Probability => (p : ℝ) - m) (1 / 4 : ℝ≥0) μ := by
      norm_num at h
      exact h
    exact h'.neg
  have hY := bernoulli_centered_subgaussian hq
  have hFp : HasSubgaussianMGF (fun r : Round => -((r.1 : ℝ) - m))
      (1 / 4 : ℝ≥0) (μ.prod (bernoulliMeasure q)) := by
    have hmap : (μ.prod (bernoulliMeasure q)).map (Prod.fst : Round → Probability) = μ := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact HasSubgaussianMGF.of_map (X := fun p : Probability => -((p : ℝ) - m))
      (Y := Prod.fst) measurable_fst.aemeasurable (hmap.symm ▸ hF)
  have hYp : HasSubgaussianMGF (fun r : Round => (if r.2 then (1 : ℝ) else 0) - q)
      (1 / 4 : ℝ≥0) (μ.prod (bernoulliMeasure q)) := by
    have hmap : (μ.prod (bernoulliMeasure q)).map (Prod.snd : Round → Bool) = bernoulliMeasure q := by
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact HasSubgaussianMGF.of_map measurable_snd.aemeasurable (hmap.symm ▸ hY)
  have hindep : IndepFun (fun r : Round => -((r.1 : ℝ) - m))
      (fun r : Round => (if r.2 then (1 : ℝ) else 0) - q) (μ.prod (bernoulliMeasure q)) := by
    exact indepFun_prod (μ := μ) (ν := bernoulliMeasure q)
      (X := fun p : Probability => -((p : ℝ) - m))
      (Y := fun y : Bool => (if y then (1 : ℝ) else 0) - q)
      (by fun_prop) (measurable_of_finite _)
  have h := hFp.add_of_indepFun hYp hindep
  norm_num at h
  convert h using 1
  funext r
  dsimp only [m]
  ring

/-- Explicit exponential form of the randomized one-step estimate in Appendix A.1. -/
theorem simultaneous_step_mgf_le (μ : Measure Probability) [IsProbabilityMeasure μ]
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    (∫ r : Round, Real.exp (t * (((if r.2 then (1 : ℝ) else 0) - q) -
      ((r.1 : ℝ) - ∫ p : Probability, (p : ℝ) ∂μ))) ∂μ.prod (bernoulliMeasure q)) ≤
      Real.exp (t ^ 2 / 4) := by
  have h := (simultaneous_step_subgaussian μ hq).mgf_le t
  have heq : ((1 / 2 : ℝ≥0) : ℝ) * t ^ 2 / 2 = t ^ 2 / 4 := by norm_num; ring
  rw [heq] at h
  exact h

/-- A deterministic current forecast removes the second centered summand. -/
theorem deterministic_step_subgaussian (p : Probability) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    HasSubgaussianMGF
      (fun r : Round => ((if r.2 then (1 : ℝ) else 0) - q) - ((r.1 : ℝ) - (p : ℝ)))
      (1 / 4 : ℝ≥0) ((Measure.dirac p).prod (bernoulliMeasure q)) := by
  have hY := bernoulli_centered_subgaussian hq
  have hYp : HasSubgaussianMGF (fun r : Round => (if r.2 then (1 : ℝ) else 0) - q)
      (1 / 4 : ℝ≥0) ((Measure.dirac p).prod (bernoulliMeasure q)) := by
    have hmap : ((Measure.dirac p).prod (bernoulliMeasure q)).map (Prod.snd : Round → Bool) =
        bernoulliMeasure q := by rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact HasSubgaussianMGF.of_map measurable_snd.aemeasurable (hmap.symm ▸ hY)
  apply hYp.congr
  have hp : ∀ᵐ r : Round ∂((Measure.dirac p).prod (bernoulliMeasure q)), r.1 = p := by
    have hmap : ((Measure.dirac p).prod (bernoulliMeasure q)).map (Prod.fst : Round → Probability) =
        Measure.dirac p := by rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_of_ae_map measurable_fst.aemeasurable (p := fun x : Probability => x = p)
      (by rw [hmap]; simp)
  filter_upwards [hp] with r hr
  simp [hr]

/-- Explicit exponential form of the deterministic one-step estimate in Appendix A.3. -/
theorem deterministic_step_mgf_le (p : Probability) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    (∫ r : Round, Real.exp (t * (((if r.2 then (1 : ℝ) else 0) - q) -
      ((r.1 : ℝ) - (p : ℝ)))) ∂(Measure.dirac p).prod (bernoulliMeasure q)) ≤
      Real.exp (t ^ 2 / 8) := by
  have h := (deterministic_step_subgaussian p hq).mgf_le t
  have heq : ((1 / 4 : ℝ≥0) : ℝ) * t ^ 2 / 2 = t ^ 2 / 8 := by norm_num; ring
  rw [heq] at h
  exact h

end CalibrationDistance.Protocol
