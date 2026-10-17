import Paper08.ZeroFree
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Actual exponential integrals along affine real interpolation

The finite-measure statement applies directly to a cube or to the integration
variables of a partial cube average. Differentiation uses an integrable local
dominating bound; no differentiability or answer certificate is assumed.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Paper08.CubeExponentialPath

variable {α : Type*} [MeasurableSpace α]

/-- The actual integral along the affine interpolation `A+tB`. -/
def affineIntegral (μ : Measure α) (A B : α → ℂ) (t : ℝ) : ℂ :=
  ∫ x, Complex.exp (A x+(t : ℂ)*B x) ∂μ

/-- Its actual differentiated integrand. -/
def affineDerivative (μ : Measure α) (A B : α → ℂ) (t : ℝ) : ℂ :=
  ∫ x, B x*Complex.exp (A x+(t : ℂ)*B x) ∂μ

lemma norm_affine_exp_le {u v : ℂ} {M C : ℝ} (hu : ‖u‖ ≤ M) (hv : ‖v‖ ≤ C) (t : ℝ) :
    ‖Complex.exp (u+(t : ℂ)*v)‖ ≤ Real.exp (M+|t| *C) := by
  apply (Complex.norm_exp_le_exp_norm _).trans
  apply Real.exp_le_exp.mpr
  calc
    ‖u+(t : ℂ)*v‖ ≤ ‖u‖+‖(t : ℂ)*v‖ := norm_add_le _ _
    _ ≤ M+|t| *C := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact add_le_add hu (mul_le_mul_of_nonneg_left hv (abs_nonneg t))

/-- Both the derivative formula and continuity of that actual derivative hold
at every real interpolation parameter, including outside `[0,1]`. -/
theorem hasDerivAt_and_continuousAt (μ : Measure α) [IsFiniteMeasure μ]
    {A B : α → ℂ} {M C : ℝ} (hC : 0 ≤ C)
    (hA : AEStronglyMeasurable A μ) (hB : AEStronglyMeasurable B μ)
    (hboundA : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) (hboundB : ∀ᵐ x ∂μ, ‖B x‖ ≤ C) (t : ℝ) :
    HasDerivAt (affineIntegral μ A B) (affineDerivative μ A B t) t ∧
      ContinuousAt (affineDerivative μ A B) t := by
  let F : ℝ → α → ℂ := fun u x => Complex.exp (A x+(u : ℂ)*B x)
  let D : ℝ → α → ℂ := fun u x => B x*F u x
  let K : ℝ := C*Real.exp (M+(|t|+1)*C)
  have hFmeas : ∀ u : ℝ, AEStronglyMeasurable (F u) μ := fun u =>
    Complex.continuous_exp.comp_aestronglyMeasurable (hA.add (hB.const_mul (u : ℂ)))
  have hDmeas : ∀ u : ℝ, AEStronglyMeasurable (D u) μ := fun u => hB.mul (hFmeas u)
  have hFint : Integrable (F t) μ := by
    apply (integrable_const (Real.exp (M+|t| *C))).mono' (hFmeas t)
    filter_upwards [hboundA,hboundB] with x hxA hxB
    exact norm_affine_exp_le hxA hxB t
  have hKint : Integrable (fun _ : α => K) μ := integrable_const K
  have hlocal : ∀ᵐ x ∂μ, ∀ u ∈ Metric.ball t 1, ‖D u x‖ ≤ K := by
    filter_upwards [hboundA,hboundB] with x hxA hxB
    intro u hu
    have hdist : |u-t| < 1 := by simpa only [Metric.mem_ball,dist_eq_norm,Real.norm_eq_abs] using hu
    have huabs : |u| ≤ |t|+1 := by
      calc
        |u| = |u-t+t| := by congr 1; ring
        _ ≤ |u-t|+|t| := abs_add_le _ _
        _ ≤ |t|+1 := by linarith
    have hexp : ‖F u x‖ ≤ Real.exp (M+(|t|+1)*C) :=
      (norm_affine_exp_le hxA hxB u).trans (Real.exp_le_exp.mpr (by nlinarith))
    dsimp only [D,K]
    rw [norm_mul]
    exact mul_le_mul hxB hexp (norm_nonneg _) hC
  have hdiff : ∀ᵐ x ∂μ, ∀ u ∈ Metric.ball t 1, HasDerivAt (fun u => F u x) (D u x) u := by
    exact Eventually.of_forall fun x u _ => by
      have hlin : HasDerivAt (fun u : ℝ => A x+(u : ℂ)*B x) (B x) u := by
        have hcast : HasDerivAt (fun u : ℝ => (u : ℂ)) (1 : ℂ) u := by
          simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one] using
            (Complex.ofRealCLM.hasDerivAt (x := u))
        simpa only [one_mul] using (hcast.mul_const (B x)).const_add (A x)
      simpa only [F,D,mul_comm] using hlin.cexp
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (bound := fun _ => K) (by norm_num : (0 : ℝ) < 1)
    (Eventually.of_forall hFmeas) hFint (hDmeas t) hlocal hKint hdiff).2
  have hc : ContinuousAt (fun u => ∫ x, D u x ∂μ) t := by
    apply continuousAt_of_dominated (μ := μ) (bound := fun _ => K)
      (Eventually.of_forall hDmeas) ?_ hKint ?_
    · filter_upwards [Metric.ball_mem_nhds t (by norm_num : (0 : ℝ) < 1)] with u hu
      exact hlocal.mono (fun x hx => hx u hu)
    · exact Eventually.of_forall fun x => by dsimp only [D,F]; fun_prop
  exact ⟨hd,hc⟩

theorem hasDerivAt_affineIntegral (μ : Measure α) [IsFiniteMeasure μ]
    {A B : α → ℂ} {M C : ℝ} (hC : 0 ≤ C)
    (hA : AEStronglyMeasurable A μ) (hB : AEStronglyMeasurable B μ)
    (hboundA : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) (hboundB : ∀ᵐ x ∂μ, ‖B x‖ ≤ C) (t : ℝ) :
    HasDerivAt (affineIntegral μ A B) (affineDerivative μ A B t) t :=
  (hasDerivAt_and_continuousAt μ hC hA hB hboundA hboundB t).1

theorem continuous_affineDerivative (μ : Measure α) [IsFiniteMeasure μ]
    {A B : α → ℂ} {M C : ℝ} (hC : 0 ≤ C)
    (hA : AEStronglyMeasurable A μ) (hB : AEStronglyMeasurable B μ)
    (hboundA : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) (hboundB : ∀ᵐ x ∂μ, ‖B x‖ ≤ C) :
    Continuous (affineDerivative μ A B) :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_and_continuousAt μ hC hA hB hboundA hboundB t).2


/-- Real potentials with the original complex activity outside the affine sum. -/
def realIntegral (μ : Measure α) (base delta : α → ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  ∫ x, Complex.exp (z*((base x : ℂ)+(t : ℂ)*(delta x : ℂ))) ∂μ

def realDerivative (μ : Measure α) (base delta : α → ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  z*∫ x, (delta x : ℂ)*Complex.exp (z*((base x : ℂ)+(t : ℂ)*(delta x : ℂ))) ∂μ

lemma affineIntegral_real_eq (μ : Measure α) (base delta : α → ℝ) (z : ℂ) :
    affineIntegral μ (fun x => z*(base x : ℂ)) (fun x => z*(delta x : ℂ)) =
      realIntegral μ base delta z := by
  funext t
  unfold affineIntegral realIntegral
  apply integral_congr_ae
  exact Eventually.of_forall fun x => congrArg Complex.exp (by ring)

lemma affineDerivative_real_eq (μ : Measure α) (base delta : α → ℝ) (z : ℂ) :
    affineDerivative μ (fun x => z*(base x : ℂ)) (fun x => z*(delta x : ℂ)) =
      realDerivative μ base delta z := by
  funext t
  unfold affineDerivative realDerivative
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    have heq : z*(base x : ℂ)+(t : ℂ)*(z*(delta x : ℂ)) =
        z*((base x : ℂ)+(t : ℂ)*(delta x : ℂ)) := by ring
    simp only [heq,mul_assoc]

/-- The parameter derivative in the exact `z * integral(delta * exp(...))`
form needed by a partial-expectation interpolation. -/
theorem real_hasDerivAt_and_continuous (μ : Measure α) [IsFiniteMeasure μ]
    {base delta : α → ℝ} {M C : ℝ} (hC : 0 ≤ C)
    (hbase : AEStronglyMeasurable base μ) (hdelta : AEStronglyMeasurable delta μ)
    (hboundBase : ∀ᵐ x ∂μ, |base x| ≤ M) (hboundDelta : ∀ᵐ x ∂μ, |delta x| ≤ C) (z : ℂ) :
    (∀ t : ℝ, HasDerivAt (realIntegral μ base delta z) (realDerivative μ base delta z t) t) ∧
      Continuous (realDerivative μ base delta z) := by
  have hA : AEStronglyMeasurable (fun x => z*(base x : ℂ)) μ :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hbase).const_mul z
  have hB : AEStronglyMeasurable (fun x => z*(delta x : ℂ)) μ :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hdelta).const_mul z
  have hAb : ∀ᵐ x ∂μ, ‖z*(base x : ℂ)‖ ≤ ‖z‖*M := by
    filter_upwards [hboundBase] with x hx
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg z)
  have hBb : ∀ᵐ x ∂μ, ‖z*(delta x : ℂ)‖ ≤ ‖z‖*C := by
    filter_upwards [hboundDelta] with x hx
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg z)
  have hCz : 0 ≤ ‖z‖*C := mul_nonneg (norm_nonneg z) hC
  constructor
  · intro t
    simpa only [affineIntegral_real_eq,affineDerivative_real_eq] using
      hasDerivAt_affineIntegral μ hCz hA hB hAb hBb t
  · simpa only [affineDerivative_real_eq] using
      continuous_affineDerivative μ hCz hA hB hAb hBb

/-- Direct specialization to the original unit cube and continuous real
potentials. Both bounds are ordinary pointwise bounds on the cube. -/
theorem cube_hasDerivAt_and_continuous {n : ℕ} {base delta : (Fin n → ℝ) → ℝ}
    {M C : ℝ} (hC : 0 ≤ C)
    (hbase : ContinuousOn base (Integral.cube n)) (hdelta : ContinuousOn delta (Integral.cube n))
    (hboundBase : ∀ x ∈ Integral.cube n, |base x| ≤ M)
    (hboundDelta : ∀ x ∈ Integral.cube n, |delta x| ≤ C) (z : ℂ) :
    (∀ t : ℝ, HasDerivAt (realIntegral (volume.restrict (Integral.cube n)) base delta z)
      (realDerivative (volume.restrict (Integral.cube n)) base delta z t) t) ∧
    Continuous (realDerivative (volume.restrict (Integral.cube n)) base delta z) := by
  let μ : Measure (Fin n → ℝ) := volume.restrict (Integral.cube n)
  letI : IsFiniteMeasure μ := ⟨by simpa only [μ,Measure.restrict_apply_univ] using Integral.volume_cube_lt_top n⟩
  have hbasem : AEStronglyMeasurable base μ := (hbase.integrableOn_compact (ZeroFree.isCompact_cube n)).1
  have hdeltam : AEStronglyMeasurable delta μ := (hdelta.integrableOn_compact (ZeroFree.isCompact_cube n)).1
  apply real_hasDerivAt_and_continuous μ (M := M) (C := C) hC hbasem hdeltam ?_ ?_ z
  · filter_upwards [ae_restrict_mem (Integral.measurableSet_cube n)] with x hx
    exact hboundBase x hx
  · filter_upwards [ae_restrict_mem (Integral.measurableSet_cube n)] with x hx
    exact hboundDelta x hx

end Paper08.CubeExponentialPath
