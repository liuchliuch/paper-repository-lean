import Paper26.ContinuousPOVM
import Paper26.TailConvexity
import Paper26.PositiveLossBridge
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Weighted trace Cauchy--Schwarz and measured SLD information

All objects are actual finite complex matrices and actual dominated POVMs.
The weighted trace inequality is proved from the nonnegative polynomial
`Tr[ρ (H-tI) E (H-tI)]`; no Cauchy--Schwarz or measured-information theorem
is supplied as an external field.  Zero Born probabilities are included.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.WeightedTraceCS

open QuantumModel TailConvexity ContinuousPOVM

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

lemma pairing_smul_right (t : ℝ) (X Y : Matrix ι ι ℂ) :
    pairing X (t • Y) = t * pairing X Y := by
  simp [pairing, Matrix.trace_smul]

/-- Reversing three Hermitian factors conjugates their trace and preserves its real part. -/
theorem triple_real_flip (ρ E H : Matrix ι ι ℂ)
    (hρ : ρ.IsHermitian) (hE : E.IsHermitian) (hH : H.IsHermitian) :
    pairing ρ (E * H) = pairing ρ (H * E) := by
  calc
    _ = (Matrix.trace (ρ * E * H)).re := by simp only [pairing, Matrix.mul_assoc]
    _ = (Matrix.trace (ρ * E * H)ᴴ).re := by
      simp only [Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re]
    _ = (Matrix.trace (H * E * ρ)).re := by
      simp only [Matrix.conjTranspose_mul, hH.eq, hE.eq, hρ.eq, Matrix.mul_assoc]
    _ = (Matrix.trace (ρ * H * E)).re :=
      congrArg Complex.re (Matrix.trace_mul_cycle H E ρ)
    _ = pairing ρ (H * E) := by simp only [pairing, Matrix.mul_assoc]

/-- The exact real quadratic polynomial is nonnegative for every real shift. -/
theorem weighted_quadratic_nonneg (ρ E H : Matrix ι ι ℂ)
    (hρ : ρ.PosSemidef) (hE : E.PosSemidef) (hH : H.IsHermitian) (t : ℝ) :
    0 ≤ pairing ρ (H * E * H) - 2 * t * pairing ρ (E * H) +
      t ^ 2 * pairing ρ E := by
  let K := H - t • (1 : Matrix ι ι ℂ)
  have hK : K.IsHermitian := by
    simp only [K, Matrix.IsHermitian, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH.eq, star_trivial]
  have hKEK : (K * E * K).PosSemidef := by
    simpa only [hK.eq] using hE.mul_mul_conjTranspose_same K
  have hn := pairing_nonneg_psd ρ _ hρ hKEK
  have hexp : pairing ρ (K * E * K) =
      pairing ρ (H * E * H) - 2 * t * pairing ρ (E * H) + t ^ 2 * pairing ρ E := by
    dsimp only [K]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, pairing_sub_right, pairing_smul_right]
    rw [triple_real_flip ρ E H hρ.isHermitian hE.isHermitian hH]
    ring
  rwa [hexp] at hn

/-- Elementary discriminant argument, including the degenerate `p=0` case. -/
theorem scalar_weighted_cs (a b p : ℝ) (hp : 0 ≤ p)
    (hq : ∀ t : ℝ, 0 ≤ a - 2 * t * b + t ^ 2 * p) :
    b ^ 2 ≤ a * p ∧ (p = 0 → b = 0) := by
  have hzero : p = 0 → b = 0 := by
    intro hp0
    by_contra hb
    have h := hq ((a + 1) / (2 * b))
    have heq : a - 2 * ((a + 1) / (2 * b)) * b = -1 := by
      field_simp
      ring
    simp only [hp0, mul_zero, add_zero, heq] at h
    norm_num at h
  refine ⟨?_, hzero⟩
  by_cases hp0 : p = 0
  · rw [hp0, hzero hp0]
    simp
  · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    have h := mul_nonneg (hq (b / p)) hp
    have heq : (a - 2 * (b / p) * b + (b / p) ^ 2 * p) * p = a * p - b ^ 2 := by
      field_simp
      ring
    rw [heq] at h
    linarith

/-- Weighted trace Cauchy--Schwarz for arbitrary PSD weights and effects. -/
theorem weighted_trace_cs (ρ E H : Matrix ι ι ℂ)
    (hρ : ρ.PosSemidef) (hE : E.PosSemidef) (hH : H.IsHermitian) :
    pairing ρ (E * H) ^ 2 ≤ pairing ρ (H * E * H) * pairing ρ E ∧
      (pairing ρ E = 0 → pairing ρ (E * H) = 0) :=
  scalar_weighted_cs _ _ _ (pairing_nonneg_psd ρ E hρ hE)
    (weighted_quadratic_nonneg ρ E H hρ hE hH)

/-- Actual SLD tangent matrix `(ρH+Hρ)/2`, with the real scalar convention. -/
def sldTangent (ρ H : Matrix ι ι ℂ) : Matrix ι ι ℂ := (1 / 2 : ℝ) • (ρ * H + H * ρ)

/-- The symmetric derivative is the real weighted cross trace. -/
theorem sldTangent_pairing (ρ E H : Matrix ι ι ℂ)
    (hρ : ρ.IsHermitian) (hE : E.IsHermitian) (hH : H.IsHermitian) :
    pairing (sldTangent ρ H) E = pairing ρ (E * H) := by
  rw [sldTangent, pairing_smul_left, pairing_add_left, pairing_mul_assoc,
    pairing_cycle H ρ E, ← triple_real_flip ρ E H hρ hE hH]
  ring

/-- Moving the first Hermitian factor around the trace identifies the positive integrand. -/
theorem quadratic_pairing_cycle (ρ E H : Matrix ι ι ℂ) :
    pairing (H * ρ * H) E = pairing ρ (H * E * H) := by
  unfold pairing
  congr 1
  calc
    Matrix.trace (H * ρ * H * E) = Matrix.trace (H * (ρ * (H * E))) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (ρ * (H * E) * H) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (ρ * (H * E * H)) := by simp only [Matrix.mul_assoc]

/-- Directional Born derivative for an actual matrix tangent. -/
def derivative (M : DominatedPOVM ι Ω) (T : Matrix ι ι ℂ) (y : Ω) : ℝ :=
  pairing T (M.effect y)

/-- The directional quantity is the actual derivative of the affine matrix Born law. -/
theorem born_tangent_affine (M : DominatedPOVM ι Ω) (ρ : Density ι)
    (T : Matrix ι ι ℂ) (y : Ω) (t : ℝ) :
    pairing (ρ.matrix + t • T) (M.effect y) = M.born ρ y + t * derivative M T y := by
  rw [pairing_add_left, pairing_smul_left]
  rfl

theorem hasDerivAt_born_tangent (M : DominatedPOVM ι Ω) (ρ : Density ι)
    (T : Matrix ι ι ℂ) (y : Ω) (t : ℝ) :
    HasDerivAt (fun u : ℝ => pairing (ρ.matrix + u • T) (M.effect y))
      (derivative M T y) t := by
  simp_rw [born_tangent_affine]
  simpa only [zero_add, one_mul] using
    (hasDerivAt_const t (M.born ρ y)).add ((hasDerivAt_id t).mul_const (derivative M T y))

/-- Classical scalar directional information density, retaining its zero-probability branch. -/
def fisherDensity (M : DominatedPOVM ι Ω) (ρ : Density ι)
    (T : Matrix ι ι ℂ) (y : Ω) : ℝ :=
  if M.born ρ y = 0 then 0 else (derivative M T y) ^ 2 / M.born ρ y

/-- The actual measured scalar directional Fisher information. -/
def measuredFisher (M : DominatedPOVM ι Ω) (ρ : Density ι) (T : Matrix ι ι ℂ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (fisherDensity M ρ T y) ∂M.reference

/-- The positive quadratic trace controlling the measured information density. -/
def quadraticDensity (M : DominatedPOVM ι Ω) (ρ : Density ι)
    (H : Matrix ι ι ℂ) (y : Ω) : ℝ := pairing ρ.matrix (H * M.effect y * H)

/-- Pointwise measured SLD inequality, with no invertibility requirement on the state. -/
theorem fisherDensity_sld_le (M : DominatedPOVM ι Ω) (ρ : Density ι)
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) {y : Ω} (hy : (M.effect y).PosSemidef) :
    0 ≤ fisherDensity M ρ (sldTangent ρ.matrix H) y ∧
      fisherDensity M ρ (sldTangent ρ.matrix H) y ≤ quadraticDensity M ρ H y := by
  have hp : 0 ≤ M.born ρ y := M.born_nonneg ρ hy
  have ha : 0 ≤ quadraticDensity M ρ H y := by
    apply pairing_nonneg_psd _ _ ρ.positive
    simpa only [hH.eq] using hy.mul_mul_conjTranspose_same H
  have hcs := (weighted_trace_cs ρ.matrix (M.effect y) H ρ.positive hy hH).1
  have hd : derivative M (sldTangent ρ.matrix H) y = pairing ρ.matrix (M.effect y * H) :=
    sldTangent_pairing _ _ _ ρ.hermitian hy.isHermitian hH
  unfold fisherDensity
  split_ifs with hz
  · exact ⟨le_rfl, ha⟩
  · have hp' : 0 < M.born ρ y := lt_of_le_of_ne hp (Ne.symm hz)
    refine ⟨div_nonneg (sq_nonneg _) hp, ?_⟩
    apply (div_le_iff₀ hp').mpr
    rw [hd]
    exact hcs

/-- Zero Born probability forces the SLD directional derivative to vanish. -/
theorem derivative_sld_zero_of_born_zero (M : DominatedPOVM ι Ω) (ρ : Density ι)
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) {y : Ω}
    (hy : (M.effect y).PosSemidef) (hp : M.born ρ y = 0) :
    derivative M (sldTangent ρ.matrix H) y = 0 := by
  rw [derivative, sldTangent_pairing _ _ _ ρ.hermitian hy.isHermitian hH]
  exact (weighted_trace_cs _ _ _ ρ.positive hy hH).2 hp

/-- An arbitrary fixed complex matrix has an integrable POVM trace pairing. -/
theorem trace_effect_integrable (M : DominatedPOVM ι Ω) (B : Matrix ι ι ℂ) :
    Integrable (fun y => Matrix.trace (B * M.effect y)) M.reference := by
  change Integrable (fun y => ∑ i, ∑ j, B i j * M.effect y j i) M.reference
  exact integrable_finset_sum Finset.univ fun i _ =>
    integrable_finset_sum Finset.univ fun j _ =>
      (M.entry_integrable j i).const_mul (B i j)

/-- The entrywise total-identity condition integrates every actual matrix trace. -/
theorem trace_effect_integral (M : DominatedPOVM ι Ω) (B : Matrix ι ι ℂ) :
    ∫ y, Matrix.trace (B * M.effect y) ∂M.reference = Matrix.trace B := by
  change (∫ y, ∑ i, ∑ j, B i j * M.effect y j i ∂M.reference) = Matrix.trace B
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ =>
      (M.entry_integrable j i).const_mul (B i j)))]
  simp_rw [integral_finset_sum Finset.univ (fun j _ =>
    (M.entry_integrable j _).const_mul (B _ j))]
  simp_rw [integral_const_mul, M.total]
  simp [Matrix.trace, Matrix.one_apply]

theorem derivative_measurable (M : DominatedPOVM ι Ω) (T : Matrix ι ι ℂ) :
    Measurable (derivative M T) := by
  have hm : Measurable (fun y => Matrix.trace (T * M.effect y)) := by
    change Measurable (fun y => ∑ i, ∑ j, T i j * M.effect y j i)
    exact Finset.measurable_sum Finset.univ fun i _ =>
      Finset.measurable_sum Finset.univ fun j _ =>
        (M.entry_measurable j i).const_mul (T i j)
  exact hm.re

theorem derivative_integrable (M : DominatedPOVM ι Ω) (T : Matrix ι ι ℂ) :
    Integrable (derivative M T) M.reference := (trace_effect_integrable M T).re

theorem derivative_integral (M : DominatedPOVM ι Ω) (T : Matrix ι ι ℂ) :
    ∫ y, derivative M T y ∂M.reference = (Matrix.trace T).re := by
  calc
    _ = (∫ y, Matrix.trace (T * M.effect y) ∂M.reference).re := by
      simpa only [derivative, pairing, RCLike.re_eq_complex_re] using
        integral_re (trace_effect_integrable M T)
    _ = _ := by rw [trace_effect_integral]

lemma quadraticDensity_eq_derivative (M : DominatedPOVM ι Ω) (ρ : Density ι)
    (H : Matrix ι ι ℂ) : quadraticDensity M ρ H = derivative M (H * ρ.matrix * H) := by
  funext y
  exact (quadratic_pairing_cycle _ _ _).symm

theorem quadraticDensity_integrable (M : DominatedPOVM ι Ω) (ρ : Density ι)
    (H : Matrix ι ι ℂ) : Integrable (quadraticDensity M ρ H) M.reference := by
  rw [quadraticDensity_eq_derivative]
  exact derivative_integrable _ _

/-- Integrating the positive controlling integrand gives exactly `Re Tr[ρ H²]`. -/
theorem quadraticDensity_integral (M : DominatedPOVM ι Ω) (ρ : Density ι)
    (H : Matrix ι ι ℂ) :
    ∫ y, quadraticDensity M ρ H y ∂M.reference = pairing ρ.matrix (H * H) := by
  rw [quadraticDensity_eq_derivative, derivative_integral]
  unfold pairing
  congr 1
  calc
    Matrix.trace (H * ρ.matrix * H) = Matrix.trace (H * (ρ.matrix * H)) := by
      rw [Matrix.mul_assoc]
    _ = Matrix.trace (ρ.matrix * H * H) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (ρ.matrix * (H * H)) := by rw [Matrix.mul_assoc]

theorem fisherDensity_measurable (M : DominatedPOVM ι Ω) (ρ : Density ι)
    (T : Matrix ι ι ℂ) : Measurable (fisherDensity M ρ T) := by
  exact Measurable.ite (measurableSet_eq_fun (M.born_measurable ρ) measurable_const)
    measurable_const (((derivative_measurable M T).pow_const 2).div (M.born_measurable ρ))

/-- Measured SLD information is genuinely integrable, including zero Born outcomes. -/
theorem fisherDensity_sld_integrable (M : DominatedPOVM ι Ω) (ρ : Density ι)
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    Integrable (fisherDensity M ρ (sldTangent ρ.matrix H)) M.reference := by
  apply (quadraticDensity_integrable M ρ H).mono'
    (fisherDensity_measurable M ρ _).aestronglyMeasurable
  filter_upwards [M.positive_ae] with y hy
  have h := fisherDensity_sld_le M ρ H hH hy
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2

/-- The actual real-integral measured SLD bound for arbitrary measurable outcome spaces. -/
theorem integral_fisherDensity_sld_le (M : DominatedPOVM ι Ω) (ρ : Density ι)
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    ∫ y, fisherDensity M ρ (sldTangent ρ.matrix H) y ∂M.reference ≤
      pairing ρ.matrix (H * H) := by
  calc
    _ ≤ ∫ y, quadraticDensity M ρ H y ∂M.reference :=
      integral_mono_ae (fisherDensity_sld_integrable M ρ H hH)
        (quadraticDensity_integrable M ρ H)
        (M.positive_ae.mono fun _ hy => (fisherDensity_sld_le M ρ H hH hy).2)
    _ = _ := quadraticDensity_integral M ρ H

/-- The measured directional Fisher bound in the actual nonnegative-integral convention. -/
theorem measuredFisher_sld_le (M : DominatedPOVM ι Ω) (ρ : Density ι)
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    measuredFisher M ρ (sldTangent ρ.matrix H) ≤
      ENNReal.ofReal (pairing ρ.matrix (H * H)) := by
  have hnonneg : 0 ≤ᵐ[M.reference] fisherDensity M ρ (sldTangent ρ.matrix H) :=
    M.positive_ae.mono fun _ hy => (fisherDensity_sld_le M ρ H hH hy).1
  rw [measuredFisher, ← ofReal_integral_eq_lintegral_ofReal
    (fisherDensity_sld_integrable M ρ H hH) hnonneg]
  exact ENNReal.ofReal_le_ofReal (integral_fisherDensity_sld_le M ρ H hH)

/-- The intrinsic inverse-Jordan operator supplies the actual SLD of any
Hermitian tangent at a positive definite density. -/
theorem sldTangent_jordanInverse (ρ : Density ι) (T : Matrix ι ι ℂ)
    (hρ : ρ.matrix.PosDef) :
    sldTangent ρ.matrix (Normalization.jordanInverse ρ.matrix T) = T := by
  unfold sldTangent
  rw [Normalization.jordanInverse_equation_posDef _ _ hρ]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  norm_num
  ring

/-- Native measured SLD Fisher bound by the actual inverse-Jordan quadratic form. -/
theorem measuredFisher_le_Q (M : DominatedPOVM ι Ω) (ρ : Density ι)
    (T : Matrix ι ι ℂ) (hρ : ρ.matrix.PosDef) (hT : T.IsHermitian) :
    measuredFisher M ρ T ≤ ENNReal.ofReal (Q ρ.matrix T) := by
  let H := Normalization.jordanInverse ρ.matrix T
  have hH : H.IsHermitian := EnergyReality.jordanInverse_hermitian _ _ hρ hT.eq
  have h := measuredFisher_sld_le M ρ H hH
  rw [sldTangent_jordanInverse ρ T hρ] at h
  rw [Q_eq_quadratic ρ.matrix T hρ]
  exact h

/-- At a positive definite state every Hermitian tangent has zero derivative
on a zero Born outcome, pointwise whenever the effect is PSD. -/
theorem derivative_zero_of_born_zero_posDef (M : DominatedPOVM ι Ω) (ρ : Density ι)
    (T : Matrix ι ι ℂ) (hρ : ρ.matrix.PosDef) (hT : T.IsHermitian) {y : Ω}
    (hy : (M.effect y).PosSemidef) (hp : M.born ρ y = 0) : derivative M T y = 0 := by
  rw [← sldTangent_jordanInverse ρ T hρ]
  exact derivative_sld_zero_of_born_zero M ρ _
    (EnergyReality.jordanInverse_hermitian _ _ hρ hT.eq) hy hp

/-- Classical chi-squared integrand with its genuine singular-denominator convention. -/
def classicalChiSquaredDensity (p q : ℝ) : ℝ≥0∞ :=
  if q = 0 then (if p = 0 then 0 else ∞) else ENNReal.ofReal ((p - q) ^ 2 / q)

theorem classicalChiSquaredDensity_measurable (M : DominatedPOVM ι Ω) (ρ σ : Density ι) :
    Measurable (fun y => classicalChiSquaredDensity (M.born ρ y) (M.born σ y)) := by
  exact Measurable.ite (measurableSet_eq_fun (M.born_measurable σ) measurable_const)
    (Measurable.ite (measurableSet_eq_fun (M.born_measurable ρ) measurable_const)
      measurable_const measurable_const)
    (((((M.born_measurable ρ).sub (M.born_measurable σ)).pow_const 2).div
      (M.born_measurable σ)).ennreal_ofReal)

/-- Chi-squared divergence of the actual scalar Born laws, including continuous outcomes. -/
def measuredChiSquared (M : DominatedPOVM ι Ω) (ρ σ : Density ι) : ℝ≥0∞ :=
  ∫⁻ y, classicalChiSquaredDensity (M.born ρ y) (M.born σ y) ∂M.reference

lemma derivative_difference (M : DominatedPOVM ι Ω) (ρ σ : Density ι) (y : Ω) :
    derivative M (ρ.matrix - σ.matrix) y = M.born ρ y - M.born σ y := by
  simp only [derivative, pairing, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re,
    DominatedPOVM.born, DominatedPOVM.complexBorn]

/-- A positive reference state also handles all null Born-density outcomes correctly. -/
theorem born_zero_of_born_zero_posDef (M : DominatedPOVM ι Ω) (ρ σ : Density ι)
    (hσ : σ.matrix.PosDef) {y : Ω} (hy : (M.effect y).PosSemidef)
    (hp : M.born σ y = 0) : M.born ρ y = 0 := by
  have h := derivative_zero_of_born_zero_posDef M σ (ρ.matrix - σ.matrix) hσ
    (ρ.hermitian.sub σ.hermitian) hy hp
  rwa [derivative_difference, hp, sub_zero] at h

/-- The support-aware classical chi-squared integral is exactly the measured
directional Fisher integral for the true matrix difference. -/
theorem measuredChiSquared_eq_measuredFisher (M : DominatedPOVM ι Ω) (ρ σ : Density ι)
    (hσ : σ.matrix.PosDef) :
    measuredChiSquared M ρ σ = measuredFisher M σ (ρ.matrix - σ.matrix) := by
  apply lintegral_congr_ae
  filter_upwards [M.positive_ae] with y hy
  by_cases hp : M.born σ y = 0
  · have hz := born_zero_of_born_zero_posDef M ρ σ hσ hy hp
    simp only [classicalChiSquaredDensity, hp, hz, if_pos, fisherDensity, ENNReal.ofReal_zero]
  · simp [classicalChiSquaredDensity, hp, fisherDensity, derivative_difference]

/-- Measured classical chi-squared never exceeds the actual quantum Bures/SLD
chi-squared divergence, for every positive definite reference density and
arbitrary dominated POVM outcome sigma-algebra. -/
theorem measuredChiSquared_le_chiB (M : DominatedPOVM ι Ω) (ρ σ : Density ι)
    (hσ : σ.matrix.PosDef) : measuredChiSquared M ρ σ ≤ QuantumModel.chiB ρ σ := by
  rw [measuredChiSquared_eq_measuredFisher M ρ σ hσ,
    PositiveLossBridge.chiB_eq_standardBuresEnergy ρ σ hσ]
  exact measuredFisher_le_Q M σ (ρ.matrix - σ.matrix) hσ (ρ.hermitian.sub σ.hermitian)

end Paper26.WeightedTraceCS
