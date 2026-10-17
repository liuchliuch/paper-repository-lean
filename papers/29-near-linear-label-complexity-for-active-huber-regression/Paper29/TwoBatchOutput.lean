import Paper29.PilotSampling
import Paper29.FiniteBatchProbability

noncomputable section
open scoped BigOperators Classical
namespace Paper29.ProcessTools

/-- Residual vector determined entirely by the pilot center and fixed labels. -/
def pilotResidual {n d m₀ : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (b π₀ : Fin n → ℝ)
    (hp₀ : ∀ i, 0 ≤ π₀ i) (μ : Fin m₀ → Fin n) (i : Fin n) : ℝ :=
  (A.mulVec (pilotCenter A b π₀ hp₀ μ)) i - b i

/-- The second minimum-norm solve is centered at the independent pilot. -/
def mainIncrement {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (z π : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ π i) (ν : Fin m → Fin n) : Fin d → ℝ :=
  pilotCenter A (fun i => -z i) π hp ν

def twoBatchOutput {n d m₀ m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (b π₀ π : Fin n → ℝ) (hp₀ : ∀ i, 0 ≤ π₀ i) (hp : ∀ i, 0 ≤ π i)
    (ω : (Fin m₀ → Fin n) × (Fin m → Fin n)) : Fin d → ℝ :=
  pilotCenter A b π₀ hp₀ ω.1 + mainIncrement A (pilotResidual A b π₀ hp₀ ω.1) π hp ω.2

theorem mainIncrement_minimizes {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (z π : Fin n → ℝ) (hp : ∀ i, 0 ≤ π i) (ν : Fin m → Fin n) :
    ∀ h, Localization.shifted A (Sampling.importanceWeights π ν) z (mainIncrement A z π hp ν) ≤
      Localization.shifted A (Sampling.importanceWeights π ν) z h := by
  simpa only [Localization.shifted, Sampling.weightedHuber_importanceWeights,
    Sampling.sampledAffine, sub_neg_eq_add, mainIncrement] using
      pilotCenter_minimizes A (fun i => -z i) π hp ν

theorem mainIncrement_zero {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (π : Fin n → ℝ) (hp : ∀ i, 0 ≤ π i) (ν : Fin m → Fin n) :
    mainIncrement A 0 π hp ν = 0 := by
  have hnorm := Attainment.minimumNormSelection_sum_sq_le A (Sampling.importanceWeights π ν)
    (0 : Fin n → ℝ) (Sampling.importanceWeights_nonneg π hp ν) (0 : EuclideanSpace ℝ (Fin d)) (by
      intro y
      have hz : Attainment.euclideanHuber A (Sampling.importanceWeights π ν) 0 0 = 0 := by
        simp [Attainment.euclideanHuber, Attainment.affineHuber, weightedHuber]
      rw [hz]
      exact weightedHuber_nonneg _ _ (Sampling.importanceWeights_nonneg π hp ν))
  have he : (∑ j, (mainIncrement A 0 π hp ν j)^2) = 0 := by
    apply le_antisymm
    · simpa [mainIncrement, pilotCenter] using hnorm
    · exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  funext j
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (mainIncrement A 0 π hp ν k))).mp he j (Finset.mem_univ j)
  simpa using sq_eq_zero_iff.mp hj

/-- Exact connection of the literal centered event to the deterministic
localization theorem, including cancellation of the affine baseline. -/
theorem centeredEvent_localization_bridge {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (z π : Fin n → ℝ) (ν : Fin m → Fin n) (η : ℝ)
    (he : CenteredTransferEvent A z π (16*baseline z) (η*baseline z) ν) :
    Localization.CenteredEvent A (fun _ => 1) (Sampling.importanceWeights π ν) z η (baseline z) := by
  intro h hh
  have hh' : unshifted A h ≤ 16*baseline z := by simpa only [Localization.phi_unit] using hh
  have hg := he h hh'
  have hs (k : Fin d → ℝ) : Localization.shifted A (Sampling.importanceWeights π ν) z k =
      Sampling.sampledShifted π ν A z k := by
    rw [Localization.shifted, Sampling.weightedHuber_importanceWeights]
    congr 1
    funext i
    ring
  have hu (k : Fin d → ℝ) : Localization.shifted A (fun _ => 1) z k = trueShifted A z k := by
    unfold Localization.shifted weightedHuber trueShifted
    simp only [one_mul, add_comm]
  simpa only [hs, hu] using hg

end Paper29.ProcessTools
