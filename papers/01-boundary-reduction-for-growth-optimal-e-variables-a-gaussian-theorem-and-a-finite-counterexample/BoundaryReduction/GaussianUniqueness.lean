import BoundaryReduction.GaussianIdentifiability

open Real Set MeasureTheory ProbabilityTheory
open scoped Classical NNReal ENNReal
namespace BoundaryReduction.Gaussian

variable {d : ℕ} {Γ : Set (Space d)} [CompactSpace Γ]
variable (K : Space d →L[ℝ] Space d) (Z : Measure (Space d)) [IsGaussian Z]
variable (hcenter : (∫ x, x ∂Z) = 0)
variable (hcov : ∀ (L : StrongDual ℝ (Space d)) (v : Space d), covariance L (precisionForm K v) Z = L v)
include hcenter hcov

/-- Strict convexity of entropy and Gaussian identifiability give uniqueness of the Borel prior. -/
theorem minimizer_eq (V W : ProbabilityMeasure Γ)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v))
    (hV : ∀ U : ProbabilityMeasure Γ, mixtureEntropy K Z V ≤ mixtureEntropy K Z U)
    (hW : ∀ U : ProbabilityMeasure Γ, mixtureEntropy K Z W ≤ mixtureEntropy K Z U) : V = W := by
  let U := priorMix V W (1/2) (by norm_num)
  let gap := fun x : Space d =>
    (1/2 : ℝ)*(likelihood K (V : Measure Γ) x*phi K (V : Measure Γ) x)+
    (1/2 : ℝ)*(likelihood K (W : Measure Γ) x*phi K (W : Measure Γ) x)-
      likelihood K (U : Measure Γ) x*phi K (U : Measure Γ) x
  have hmix (x : Space d) : likelihood K (U : Measure Γ) x =
      (1/2 : ℝ)*likelihood K (V : Measure Γ) x+(1/2 : ℝ)*likelihood K (W : Measure Γ) x := by
    dsimp [U]
    rw [likelihood_mix]
    ring
  have hgap (x : Space d) : 0 ≤ gap x := by
    have h := strictConvexOn_mul_log.convexOn.2
      (likelihood_pos K (V : Measure Γ) x).le (likelihood_pos K (W : Measure Γ) x).le
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)+1/2=1)
    simp only [smul_eq_mul, ← hmix x] at h
    dsimp [gap, phi]
    linarith
  have hEV := integrable_entropy K Z (V : Measure Γ) R hR hK
  have hEW := integrable_entropy K Z (W : Measure Γ) R hR hK
  have hEU := integrable_entropy K Z (U : Measure Γ) R hR hK
  have hi : Integrable gap Z := ((hEV.const_mul (1/2)).add (hEW.const_mul (1/2))).sub hEU
  have hFE : mixtureEntropy K Z V = mixtureEntropy K Z W := le_antisymm (hV W) (hW V)
  have hgapInt : (∫ x, gap x ∂Z) = (1/2 : ℝ)*mixtureEntropy K Z V+
      (1/2 : ℝ)*mixtureEntropy K Z W-mixtureEntropy K Z U := by
    have hs := integral_sub ((hEV.const_mul (1/2)).add (hEW.const_mul (1/2))) hEU
    simp only [Pi.add_apply] at hs
    rw [show (∫ x, gap x ∂Z) = _ from hs]
    rw [integral_add_fun (hEV.const_mul (1/2)) (hEW.const_mul (1/2)), integral_const_mul, integral_const_mul]
    rfl
  have hzero : (∫ x, gap x ∂Z) = 0 := by
    have hnn : 0 ≤ ∫ x, gap x ∂Z := integral_nonneg hgap
    have hm := hV U
    rw [hgapInt] at hnn ⊢
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg hgap hi).mp hzero
  have hlik : (fun x => likelihood K (V : Measure Γ) x) =ᵐ[Z]
      fun x => likelihood K (W : Measure Γ) x := by
    filter_upwards [hae] with x hx
    by_contra hne
    have h := strictConvexOn_mul_log.2
      (likelihood_pos K (V : Measure Γ) x).le (likelihood_pos K (W : Measure Γ) x).le hne
      (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ)+1/2=1)
    simp only [smul_eq_mul, ← hmix x] at h
    dsimp [gap, phi] at hx
    linarith
  apply mixtureMeasure_injective K Z hcenter hcov R hR hK
  exact withDensity_congr_ae (hlik.mono (fun x hx => congrArg ENNReal.ofReal hx))

/-- Existence and uniqueness of the actual compact Borel entropy minimizer. -/
theorem exists_unique_entropy_minimizer (hΓ : Γ.Nonempty)
    (R : ℝ≥0) (hR : ∀ r : Γ, ‖(r : Space d)‖ ≤ R)
    (hK : ∀ v : Space d, 0 ≤ inner ℝ v (K v)) :
    ∃! W : ProbabilityMeasure Γ, ∀ V : ProbabilityMeasure Γ, mixtureEntropy K Z W ≤ mixtureEntropy K Z V := by
  obtain ⟨W,hW⟩ := exists_entropy_minimizer K Z hΓ R hR hK
  refine ⟨W,hW,?_⟩
  intro V hV
  exact minimizer_eq K Z hcenter hcov V W R hR hK hV hW

end BoundaryReduction.Gaussian
