import Paper35.GaussianWinner
import Paper35.LayerMoment

/-! The generic finite independent-mark selection identity is proved here by
an explicit finite indicator partition and mathlib's independence integral
factorization. It is not an external theorem input. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators
namespace Paper35.GaussianWinner

set_option maxHeartbeats 600000 in
/-- Arbitrary finite independent marking, fully proved. -/
theorem independentMarking : IndependentMarkingInput := by
  classical
  intro Ω inst μ instP K q X R g F Gamma hX hR hg hF hind hL hzero hcov hFX
  let E (j : Fin K) : Set Ω := {ω | g (X ω)=j}
  have hE (j : Fin K) : MeasurableSet (E j) := (hg.comp hX) (measurableSet_singleton j)
  let I (j : Fin K) (ω : Ω) : ℝ := (E j).indicator (fun _ => 1) ω
  have hI (j : Fin K) : Integrable (I j) μ := (integrable_const 1).indicator (hE j)
  have hmeasI (j : Fin K) : Measurable (I j) := measurable_const.indicator (hE j)
  have hsumI (ω : Ω) : ∑ j, I j ω=1 := by simp [I,E,Set.indicator_apply]
  have hindI (j : Fin K) (i k : Fin q) :
      IndepFun (I j) (fun ω => R ω j i*R ω j k) μ := by
    have H : IndepFun (I j) (fun ω => R ω j i*R ω j k) μ := hind.comp
      (φ := fun x => ({x | g x=j} : Set (Fin K → ℝ)).indicator (fun _ => (1:ℝ)) x)
      (ψ := fun r : Fin K → Fin q → ℝ => r j i*r j k)
      (measurable_const.indicator (hg (measurableSet_singleton j))) (by fun_prop)
    exact H
  have hselectL (i : Fin q) : MemLp (fun ω => R ω (g (X ω)) i) 2 μ :=
    Paper35.LayerMoment.memLp_finite_selection μ (fun j ω => R ω j i)
      (fun j => hL j i) (fun ω => g (X ω)) (hg.comp hX)
  refine ⟨hselectL,?_,?_⟩
  · intro i k
    have hpoint (ω : Ω) : R ω (g (X ω)) i*R ω (g (X ω)) k =
        ∑ j, I j ω*(R ω j i*R ω j k) := by simp [I,E,Set.indicator_apply]
    have hterm (j : Fin K) : Integrable (fun ω => I j ω*(R ω j i*R ω j k)) μ := by
      exact (hindI j i k).integrable_mul (hI j) ((hL j i).integrable_mul (hL j k))
    simp_rw [hpoint]
    rw [integral_finset_sum _ (fun j _ => hterm j)]
    have ht (j : Fin K) : (∫ ω, I j ω*(R ω j i*R ω j k) ∂μ) =
        (∫ ω, I j ω ∂μ)*Gamma i k := by
      rw [(hindI j i k).integral_fun_mul_eq_mul_integral
        (hI j).aestronglyMeasurable ((hL j i).integrable_mul (hL j k)).aestronglyMeasurable,hcov]
    simp_rw [ht]
    rw [← Finset.sum_mul,← integral_finset_sum _ (fun j _ => hI j)]
    simp [hsumI]
  · intro i
    let FI (j : Fin K) (ω : Ω) := (E j).indicator (fun ω => F (X ω)) ω
    have hFI (j : Fin K) : MemLp (FI j) 2 μ := hFX.indicator (hE j)
    have hindFI (j : Fin K) : IndepFun (FI j) (fun ω => R ω j i) μ := by
      exact hind.comp
        (φ := fun x => ({x | g x=j} : Set (Fin K → ℝ)).indicator F x)
        (ψ := fun r : Fin K → Fin q → ℝ => r j i)
        (hF.indicator (hg (measurableSet_singleton j))) (by fun_prop)
    have hpoint (ω : Ω) : F (X ω)*R ω (g (X ω)) i =
        ∑ j, FI j ω*R ω j i := by simp [FI,E,Set.indicator_apply]
    simp_rw [hpoint]
    have hterm (j : Fin K) : Integrable (fun ω => FI j ω*R ω j i) μ :=
      (hFI j).integrable_mul (hL j i)
    rw [integral_finset_sum _ (fun j _ => hterm j)]
    apply Finset.sum_eq_zero
    intro j hj
    rw [(hindFI j).integral_fun_mul_eq_mul_integral
      (hFI j).aestronglyMeasurable (hL j i).aestronglyMeasurable,hzero,mul_zero]

namespace GaussianUnit
variable {q : ℕ} (m : GaussianUnit q)

/-- Proposition 8.2 with only the standard Gaussian affine/regression laws as
external inputs; finite independent selection has been discharged. -/
theorem winner_secondMoment_standard (haffine : AffineGaussianLawInput)
    (hregression : GaussianRegressionInput) (n : ℕ) (z : Fin q → ℝ) :
    m.selectedSecondMoment n z =
      Paper35.Deep.activeSecondMomentMatrix m.covariance z (m.scoreVariance z)
        (Paper35.Deep.gaussianMaxSecondMoment (n+1)) :=
  m.winner_secondMoment haffine hregression independentMarking n z

end GaussianUnit
end Paper35.GaussianWinner
