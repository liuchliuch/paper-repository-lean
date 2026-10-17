import Paper29.PilotGrid
import Paper29.Attainment

noncomputable section
open scoped BigOperators Classical
namespace Paper29.ProcessTools

/-- Finite union bound for any two actual events. -/
theorem eventMass_inter_lower {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1) (E F : Finset Ω) :
    Sampling.eventMass p E + Sampling.eventMass p F - 1 ≤
      Sampling.eventMass p (E ∩ F) := by
  have hu : Sampling.eventMass p (E ∪ F) ≤ 1 := by
    have h := eventMass_mono p hp (Finset.subset_univ (E ∪ F))
    simpa only [Sampling.eventMass, hsum] using h
  have he : Sampling.eventMass p (E ∪ F) + Sampling.eventMass p (E ∩ F) =
      Sampling.eventMass p E + Sampling.eventMass p F := by
    exact Finset.sum_union_inter
  linarith

/-- Markov at a fixed comparator, including zero true optimum. -/
theorem pilot_comparator_probability {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (b : Fin n → ℝ) (xstar : Fin d → ℝ) (π : Fin n → ℝ)
    (hπ : ∀ i, 0 < π i) (hsum : ∑ i, π i = 1) (hm : 0 < m)
    {δ : ℝ} (hδ : 0 < δ) :
    1 - δ ≤ Sampling.eventMass (Sampling.iidMass π)
      (Finset.univ.filter (fun ν : Fin m → Fin n =>
        Sampling.sampledAffine π ν A b xstar ≤ objective A b xstar / δ)) := by
  have hF : 0 ≤ objective A b xstar := Finset.sum_nonneg (fun i _ => huber_nonneg _)
  by_cases hzero : objective A b xstar = 0
  · have hz := Localization.residual_zero_of_objective_zero A b xstar hzero
    have hs (ν : Fin m → Fin n) : Sampling.sampledAffine π ν A b xstar = 0 := by
      simp [Sampling.sampledAffine, Sampling.sampledHuber, Sampling.importanceAverage, hz]
    simp only [hs, hzero, zero_div, le_refl, Finset.filter_true_of_mem (fun _ _ => True.intro)]
    simp only [Sampling.eventMass, Sampling.iidMass_sum π hsum]
    linarith
  · have hpos : 0 < objective A b xstar := lt_of_le_of_ne hF (Ne.symm hzero)
    apply good_event_of_expectation (Sampling.iidMass π)
      (fun ν : Fin m → Fin n => Sampling.sampledAffine π ν A b xstar)
      (Sampling.iidMass_nonneg π (fun i => (hπ i).le)) (Sampling.iidMass_sum π hsum)
      (fun ν => Sampling.sampledHuber_nonneg π ν _ (fun i => (hπ i).le)) (div_pos hpos hδ)
    rw [← Sampling.expectation, Sampling.sampledAffine_unbiased π A b xstar hπ hsum hm]
    exact le_of_eq (by field_simp)

/-- Actual unique minimum-norm pilot center, using only pilot data. -/
def pilotCenter {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (b π : Fin n → ℝ)
    (hπ : ∀ i, 0 ≤ π i) (ν : Fin m → Fin n) : Fin d → ℝ :=
  WithLp.ofLp (Attainment.minimumNormSelection A (Sampling.importanceWeights π ν) b
    (Sampling.importanceWeights_nonneg π hπ ν))

theorem pilotCenter_minimizes {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (b π : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i) (ν : Fin m → Fin n) :
    ∀ x, Sampling.sampledAffine π ν A b (pilotCenter A b π hπ ν) ≤
      Sampling.sampledAffine π ν A b x := by
  intro x
  have h := (Attainment.minimumNormSelection_spec A (Sampling.importanceWeights π ν) b
    (Sampling.importanceWeights_nonneg π hπ ν)).1 (WithLp.toLp 2 x)
  simpa only [Attainment.euclideanHuber, Attainment.affineHuber, pilotCenter,
    WithLp.ofLp_toLp, Sampling.weightedHuber_importanceWeights, Sampling.sampledAffine] using h

/-- Complete probabilistic assembly of the pilot guarantee from its actual
embedding event. No global parameter-dependent measurable selection is needed:
for a fixed response, this sample space is finite. -/
theorem pilot_center_probability {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (b π : Fin n → ℝ) (hπ : ∀ i, 0 < π i) (hsum : ∑ i, π i = 1) (hm : 0 < m)
    (xstar : Fin d → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hembed : 1 - δ ≤ Sampling.eventMass (Sampling.iidMass π)
      (Finset.univ.filter (fun ν : Fin m → Fin n => ∀ h,
        |Sampling.sampledUnshifted π ν A h - unshifted A h| ≤
          (1 / 8) * unshifted A h))) :
    1 - 2 * δ ≤ Sampling.eventMass (Sampling.iidMass π)
      (Finset.univ.filter (fun ν : Fin m → Fin n =>
        objective A b (pilotCenter A b π (fun i => (hπ i).le) ν) ≤
          (1 + 2 / Real.sqrt ((1 - 1/8) * δ))^2 * objective A b xstar)) := by
  let E := Finset.univ.filter (fun ν : Fin m → Fin n => ∀ h,
    |Sampling.sampledUnshifted π ν A h - unshifted A h| ≤ (1/8) * unshifted A h)
  let F := Finset.univ.filter (fun ν : Fin m → Fin n =>
    Sampling.sampledAffine π ν A b xstar ≤ objective A b xstar / δ)
  have hp := fun i => (hπ i).le
  have hF := pilot_comparator_probability A b xstar π hπ hsum hm hδ
  change 1 - δ ≤ Sampling.eventMass (Sampling.iidMass π) E at hembed
  change 1 - δ ≤ Sampling.eventMass (Sampling.iidMass π) F at hF
  have hEF := eventMass_inter_lower (Sampling.iidMass π) (Sampling.iidMass_nonneg π hp)
    (Sampling.iidMass_sum π hsum) E F
  have hprob : 1 - 2*δ ≤ Sampling.eventMass (Sampling.iidMass π) (E ∩ F) := by
    calc
      1 - 2*δ = (1-δ)+(1-δ)-1 := by ring
      _ ≤ Sampling.eventMass (Sampling.iidMass π) E +
          Sampling.eventMass (Sampling.iidMass π) F - 1 :=
        sub_le_sub_right (add_le_add hembed hF) 1
      _ ≤ Sampling.eventMass (Sampling.iidMass π) (E ∩ F) := hEF
  apply hprob.trans
  apply eventMass_mono _ (Sampling.iidMass_nonneg π hp)
  intro ν hν
  obtain ⟨hE, hF⟩ := Finset.mem_inter.mp hν
  have hE' := (Finset.mem_filter.mp hE).2
  have hF' := (Finset.mem_filter.mp hF).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  apply Localization.deterministic_pilot_bound A b (Sampling.importanceWeights π ν)
    (pilotCenter A b π hp ν) xstar (Sampling.importanceWeights_nonneg π hp ν)
    (by norm_num : (1/8 : ℝ) < 1) hδ
  · intro h
    have hh := (abs_le.mp (hE' h)).1
    change _ ≤ weightedHuber _ _
    rw [Sampling.weightedHuber_importanceWeights]
    change _ ≤ Sampling.sampledUnshifted π ν A h
    linarith
  · simpa only [Localization.shifted, sub_eq_add_neg,
      Sampling.weightedHuber_importanceWeights, Sampling.sampledAffine] using hF'
  · simpa only [Localization.shifted, sub_eq_add_neg,
      Sampling.weightedHuber_importanceWeights, Sampling.sampledAffine] using
      pilotCenter_minimizes A b π hp ν

end Paper29.ProcessTools
