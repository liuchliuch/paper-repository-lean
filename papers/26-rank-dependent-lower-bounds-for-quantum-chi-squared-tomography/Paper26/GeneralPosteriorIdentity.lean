import Paper26.LikelihoodSupport

/-! Lemma 3.2 without an s-finiteness assumption on the original reference
measure. Continuity and normalized square likelihoods give a common measurable
s-finite support. Every likelihood, derivative, marginal and score contribution
outside it vanishes, so the proved weak Bayes identity applies unchanged. -/
noncomputable section
open scoped ENNReal NNReal BigOperators
open MeasureTheory Set

namespace Paper26.GeneralPosteriorIdentity
open WeakPosteriorIdentity H1PosteriorBound
variable {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}

theorem lintegral_restrict_eq_of_zero {S : Set Y} (hS : MeasurableSet S)
    (f : Y → ℝ≥0∞) (hz : ∀ᵐ y ∂ν, y ∉ S → f y = 0) :
    (∫⁻ y in S, f y ∂ν) = ∫⁻ y, f y ∂ν := by
  rw [← lintegral_indicator hS]
  apply lintegral_congr_ae
  filter_upwards [hz] with y hy
  by_cases h : y ∈ S
  · simp [h]
  · simp [h, hy h]

theorem integral_restrict_eq_of_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {S : Set Y} (hS : MeasurableSet S)
    (f : Y → F) (hz : ∀ᵐ y ∂ν, y ∉ S → f y = 0) :
    (∫ y in S, f y ∂ν) = ∫ y, f y ∂ν := by
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [hz] with y hy
  by_cases h : y ∈ S
  · simp [h]
  · simp [h, hy h]

/-- Exact general posterior information identity for arbitrary outcome
reference measure. The classical inputs are the existing weak product rule
and derivative uniqueness, not a posterior identity or a measure-support fact. -/
theorem lemma_3_2 {p : ℕ} (ν : Measure Y)
    (P : WeakLocallyLipschitzProductInput p) (U : WeakDerivativeUniquenessInput p)
    (h : WeakH1Root p) (g : Y → ParameterSpace p → ℝ)
    (hLL : ∀ᵐ y ∂ν, LocallyLipschitz (g y))
    (hg : ∀ x, AEStronglyMeasurable (fun y => g y x) ν)
    (hGjoint : AEStronglyMeasurable (fun z : Y × ParameterSpace p => g z.1 z.2)
      (ν.prod volume))
    (hDjoint : AEStronglyMeasurable
      (fun z : Y × ParameterSpace p => fderiv ℝ (g z.1) z.2) (ν.prod volume))
    (hn : ∀ x, (∫⁻ y, ENNReal.ofReal (g y x ^ 2) ∂ν) = 1)
    (K : ℕ → Set (ParameterSpace p)) (hK : ∀ n, MeasurableSet (K n))
    (hcover : ∀ x, ∃ n, x ∈ K n)
    (hfin : ∀ n, (∫⁻ x in K n,
      (∫⁻ y, ‖fderiv ℝ (g y) x‖ₑ ^ (2 : ℕ) ∂ν)) ≠ ∞)
    (hdiff : ∀ᵐ x ∂(volume : Measure (ParameterSpace p)),
      HasFDerivAt (fun t => ∫ y, g y t ^ 2 ∂ν)
        (∫ y, (2 * g y x) • fderiv ℝ (g y) x ∂ν) x) :
    (∫⁻ y, marginal h g y * (bayesPosterior P h g y).fisher ∂ν) =
      h.fisher + dataInformation ν h g := by
  have hi (x : ParameterSpace p) : Integrable (fun y => g y x ^ 2) ν :=
    (memLp_two_of_lintegral_sq_ne_top ν (hg x) (by rw [hn x]; simp)).integrable_sq
  obtain ⟨S, hS, hsf, hz⟩ := LikelihoodSupport.differentiable_likelihood_support g
    (hLL.mono fun y hy => hy.continuous) hi
  let νS := ν.restrict S
  letI : SFinite νS := hsf
  have hprod : νS.prod (volume : Measure (ParameterSpace p)) ≤ ν.prod volume := by
    apply Measure.le_iff.2
    intro T hT
    rw [Measure.prod_apply hT, Measure.prod_apply hT]
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  have heG (x : ParameterSpace p) :
      (∫⁻ y, ENNReal.ofReal (g y x ^ 2) ∂νS) = ∫⁻ y, ENNReal.ofReal (g y x ^ 2) ∂ν := by
    apply lintegral_restrict_eq_of_zero hS
    filter_upwards [hz] with y hy hnot
    rw [(hy hnot x).1]
    simp
  have heD (x : ParameterSpace p) :
      (∫⁻ y, ‖fderiv ℝ (g y) x‖ₑ ^ (2 : ℕ) ∂νS) =
        ∫⁻ y, ‖fderiv ℝ (g y) x‖ₑ ^ (2 : ℕ) ∂ν := by
    apply lintegral_restrict_eq_of_zero hS
    filter_upwards [hz] with y hy hnot
    rw [(hy hnot x).2, ← ofReal_norm, norm_zero, ENNReal.ofReal_zero, zero_pow two_ne_zero]
  have heGreal (x : ParameterSpace p) :
      (∫ y, g y x ^ 2 ∂νS) = ∫ y, g y x ^ 2 ∂ν := by
    apply integral_restrict_eq_of_zero hS
    filter_upwards [hz] with y hy hnot
    rw [(hy hnot x).1]
    simp
  have heScore (x : ParameterSpace p) :
      (∫ y, (2 * g y x) • fderiv ℝ (g y) x ∂νS) =
        ∫ y, (2 * g y x) • fderiv ℝ (g y) x ∂ν := by
    apply integral_restrict_eq_of_zero hS
    filter_upwards [hz] with y hy hnot
    rw [(hy hnot x).1]
    simp
  have hid := bayes_information_identity_of_local_energy νS P U h g
    (ae_restrict_of_ae hLL) (fun x => (hg x).restrict)
    (hGjoint.mono_measure hprod) (hDjoint.mono_measure hprod)
    (fun x => (heG x).trans (hn x)) K hK hcover
    (by intro n; simpa only [heD] using hfin n) (by
      filter_upwards [hdiff] with x hx
      convert hx using 1
      · exact funext heGreal
      · exact heScore x)
  have heL : (∫⁻ y, marginal h g y * (bayesPosterior P h g y).fisher ∂νS) =
      ∫⁻ y, marginal h g y * (bayesPosterior P h g y).fisher ∂ν := by
    apply lintegral_restrict_eq_of_zero hS
    filter_upwards [hz] with y hy hnot
    have hg0 : g y = 0 := funext fun x => (hy hnot x).1
    simp [marginal, hg0]
  have heI : dataInformation νS h g = dataInformation ν h g := by
    unfold dataInformation
    simp_rw [heD]
  rw [heL, heI] at hid
  exact hid

end Paper26.GeneralPosteriorIdentity
