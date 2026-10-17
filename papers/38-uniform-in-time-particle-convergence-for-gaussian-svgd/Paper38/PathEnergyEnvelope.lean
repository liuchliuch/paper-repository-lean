import Paper38.EnergyCompactness
import Paper38.GaussianEnergyGeometry
import Paper38.GaussianLocalization
import Paper38.StandardizedShape
import Paper38.LogEnergyLocalization

/-! The logarithmic energy envelope used on the exceptional event in Section 7.
Every quantity is the actual empirical mean/covariance or Gaussian energy. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Frobenius
namespace Paper38.PathEnergyEnvelope
open Model HilbertCoordinates

variable {d N : ℕ}
set_option maxHeartbeats 800000

lemma empirical_secondMoment (hN : 0 < N) (x : Fin N → E d) :
    (N : ℝ)⁻¹ * ∑ i, ‖x i‖ ^ 2 =
      ‖empiricalMean x‖ ^ 2 + (empiricalCovariance x).trace := by
  have h := Standardization.centered_affine_cost hN
    (fun i => ModelBridges.coordinates (x i)) (1 : Mat d)
    (-ModelBridges.coordinates (empiricalMean x))
  have he (i : Fin N) :
      (1 : Mat d) *ᵥ Empirical.centered (fun j => ModelBridges.coordinates (x j)) i -
          -ModelBridges.coordinates (empiricalMean x) = ModelBridges.coordinates (x i) := by
    rw [Matrix.one_mulVec, Empirical.centered, ← ModelBridges.empiricalMean_coordinates]
    abel
  simp_rw [he, Standardization.sqNorm_eq_euclidean] at h
  have hneg : (WithLp.toLp 2 (-ModelBridges.coordinates (empiricalMean x)) : E d) =
      -empiricalMean x := rfl
  rw [hneg, norm_neg, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one,
    ← ModelBridges.empiricalCovariance_coordinates] at h
  simpa only [ModelBridges.coordinates, WithLp.toLp_ofLp, add_comm] using h

lemma gaussian_zero : gaussianLaw (0 : E d) (0 : Mat d) = Measure.dirac 0 := by
  letI := GaussianCoupling.standardGaussian_probability d
  simp [gaussianLaw, matVec, vec, Measure.map_const]

lemma empirical_zero (hN : 0 < N) :
    empiricalLaw (fun _ : Fin N => (0 : E d)) = Measure.dirac 0 := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [GaussianCoupling.empiricalLaw_eq_transport_empirical hN]
  simp [Transport.empirical, Measure.map_const]


/-- A deterministic second-moment envelope for the actual transport error. -/
theorem empirical_gaussian_moment_bound (hN : 0 < N) (x : Fin N → E d)
    (μ : E d) (A : Mat d) :
    Transport.w2sq (empiricalLaw x) (gaussianLaw μ A) ≤
      ENNReal.ofReal (2 * (‖empiricalMean x‖ ^ 2 + (empiricalCovariance x).trace) +
        2 * (‖μ‖ ^ 2 + frobSq A)) := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  letI : IsProbabilityMeasure (empiricalLaw x) := by
    rw [GaussianCoupling.empiricalLaw_eq_transport_empirical hN]; infer_instance
  letI := GaussianAffine.gaussianLaw_probability μ A
  letI : IsProbabilityMeasure (Measure.dirac (0 : E d)) := inferInstance
  have he := StandardizedShape.empirical_coupling_cost hN x (fun _ => 0)
  rw [empirical_zero hN] at he
  simp only [sub_zero, empirical_secondMoment hN x] at he
  have hg := GaussianCoupling.gaussian_w2sq_le (0 : E d) μ (0 : Mat d) A
  rw [gaussian_zero] at hg
  have hga : ‖(0 : E d)-μ‖ ^ 2 + frobSq ((0 : Mat d)-A) = ‖μ‖ ^ 2+frobSq A := by
    simp [frobSq]
  rw [hga] at hg
  have h := (Transport.w2sq_triangle (empiricalLaw x) (Measure.dirac 0) (gaussianLaw μ A)).trans
    (add_le_add (mul_le_mul_left' he 2) (mul_le_mul_left' hg 2))
  have htr := (ModelBridges.empiricalCovariance_posSemidef x).trace_nonneg
  have hf : 0 ≤ frobSq A := Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hleft : 0 ≤ 2 * (‖empiricalMean x‖^2+(empiricalCovariance x).trace) :=
    mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) htr)
  have hright : 0 ≤ 2 * (‖μ‖^2+frobSq A) :=
    mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) hf)
  have htwo (v : ℝ) : (2 : ℝ≥0∞) * ENNReal.ofReal v = ENNReal.ofReal (2*v) := by
    simpa only [ENNReal.ofReal_ofNat] using
      (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2) (q := v)).symm
  simpa only [htwo, ENNReal.ofReal_add hleft hright] using h


lemma logdet_root_bound (C : Mat d) (hC : C.PosDef) :
    -Real.log (CFC.sqrt C).det ≤ max (-Real.log C.det) 0 := by
  have hp : 0 < (CFC.sqrt C).det := hC.posDef_sqrt.det_pos
  have hd : C.det = (CFC.sqrt C).det * (CFC.sqrt C).det := by
    rw [← Matrix.det_mul, CFC.sqrt_mul_sqrt_self C hC.posSemidef.nonneg]
  have hl : Real.log C.det = 2 * Real.log (CFC.sqrt C).det := by
    rw [hd, Real.log_mul hp.ne' hp.ne']; ring
  have h1 := le_max_left (-Real.log C.det) 0
  have h2 := le_max_right (-Real.log C.det) 0
  linarith

lemma trace_nonneg (x : Fin N → E d) : 0 ≤ (empiricalCovariance x).trace :=
  (ModelBridges.empiricalCovariance_posSemidef x).trace_nonneg

/-- The actual initial energy is bounded by the logarithmic sample envelope
(7.15), without an inverse-covariance moment. -/
theorem initialized_energy_bound {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (μ0 : E d) (S0 : Mat d)
    (ω : Sampling.Sample d N)
    (hS : (empiricalCovariance (Specification.gaussianCloud μ0 S0 N ω)).PosDef) :
    energy V (Specification.cloudQ (Specification.gaussianCloud μ0 S0 N ω)) ≤
      (|V 0|+‖fderiv ℝ V 0‖+2*β+1) * Sampling.initialEnvelope μ0 S0 N ω := by
  let x := Specification.gaussianCloud μ0 S0 N ω
  have he := EnergyCompactness.gaussian_energy_upper hV (Specification.cloudQ x)
  have hr := GaussianLocalization.frobSq_sqrt_trace (empiricalCovariance x) hS
  have hl := logdet_root_bound (empiricalCovariance x) hS
  have ht := trace_nonneg x
  have hm := sq_nonneg ‖empiricalMean x‖
  have hβ := hV.alpha_le_beta.trans' hV.alpha_pos.le
  have hC : 0 ≤ |V 0|+‖fderiv ℝ V 0‖+2*β := by positivity
  have hz : 0 ≤ max (-Real.log (empiricalCovariance x).det) 0 := le_max_right _ _
  change _ ≤ (|V 0|+‖fderiv ℝ V 0‖+2*β+1) *
    (1+‖empiricalMean x‖^2+(empiricalCovariance x).trace+
      max (-Real.log (empiricalCovariance x).det) 0)
  change energy V (empiricalMean x, covarianceRoot (empiricalCovariance x)) ≤ _ at he ⊢
  dsimp only [Specification.cloudQ, covarianceRoot] at he ⊢
  rw [hr] at he
  nlinarith [mul_nonneg hC hz]

/-- Strong convexity and actual energy trapping bound the full source Hilbert
second moment by a linear function of the initial energy. -/
theorem norm_sq_of_energy_trapping {V : E d → ℝ} {α β E0 : ℝ}
    (hV : AdmissiblePotential V α β) (z q : Tangent d)
    (hz : z ∈ Domain d) (hq : q ∈ Domain d)
    (hcrit : gradient (HilbertCoordinates.energy V) z = 0)
    (henergy : HilbertCoordinates.energy V q ≤ E0) :
    ‖q‖ ^ 2 ≤ 4/α * (E0-HilbertCoordinates.energy V z)+2*‖z‖^2 := by
  have hstrong : EnergyDecay.StrongConvexGradientOn (HilbertCoordinates.energy V)
      (gradient (HilbertCoordinates.energy V)) (Domain d) α :=
    GradientGeometry.strongConvexGradientOn_of_second_fderiv_lower
    (Domain_isOpen d) (Domain_convex d) (GaussianEnergyGeometry.intrinsic_energy_contDiffOn hV)
    (fun q hq v => GaussianEnergyGeometry.intrinsic_energy_second_fderiv_lower hV q v hq)
  have hs := hstrong z hz q hq
  rw [hcrit, inner_zero_left] at hs
  have ht : ‖q‖ ≤ ‖q-z‖+‖z‖ := by
    simpa only [sub_add_cancel] using norm_add_le (q-z) z
  have hsq : ‖q‖^2 ≤ 2*‖q-z‖^2+2*‖z‖^2 := by
    nlinarith [sq_nonneg (‖q-z‖-‖z‖), norm_nonneg q, norm_nonneg (q-z), norm_nonneg z]
  have ha := hV.alpha_pos
  have hb : ‖q‖^2 ≤ (4*(E0-HilbertCoordinates.energy V z)+2*α*‖z‖^2)/α :=
    (le_div_iff₀ ha).2 (by nlinarith [mul_le_mul_of_nonneg_left hsq ha.le])
  convert hb using 1 <;> field_simp

/-- The moment norm is the empirical second moment, in precisely the paper's
Euclidean--Frobenius coordinates. -/
lemma rootState_norm_sq (μ : E d) (C : Mat d) (hC : C.PosDef) :
    ‖GaussianLocalization.rootState μ C‖^2 = ‖μ‖^2+C.trace := by
  have h := norm_ambient_sq (toModel d (GaussianLocalization.rootState μ C))
  rw [ambient_toModel, GaussianLocalization.toModel_rootState,
    GaussianLocalization.frobSq_sqrt_trace C hC] at h
  exact h

/-- Source (7.20): one constant precedes the particle count and sample, and
controls the supremum over all physical times by the actual logarithmic initial
sample envelope. Energy trapping is a previously proved dynamical component,
not an external statistical hypothesis. -/
theorem energy_trapped_paths_envelope {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (z : Tangent d) (hz : z ∈ Domain d)
    (hcrit : gradient (HilbertCoordinates.energy V) z = 0)
    (μ0 : E d) (S0 : Mat d) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 0 < N → ∀ ω : Sampling.Sample d N,
      ∀ (p : Specification.MomentPath d) (X : Specification.ParticlePath d N),
      (∀ t, 0 ≤ t → (p.cov t).PosDef) →
      (∀ t, 0 ≤ t → (empiricalCovariance (X t)).PosDef) →
      (empiricalCovariance (Specification.gaussianCloud μ0 S0 N ω)).PosDef →
      (∀ t, 0 ≤ t → energy V (p.q t) ≤ energy V (μ0,covarianceRoot S0)) →
      (∀ t, 0 ≤ t → energy V (Specification.cloudQ (X t)) ≤
        energy V (Specification.cloudQ (Specification.gaussianCloud μ0 S0 N ω))) →
      Specification.pathSup X p ≤ ENNReal.ofReal (K * Sampling.initialEnvelope μ0 S0 N ω) := by
  let C := |V 0|+‖fderiv ℝ V 0‖+2*β+1
  let Fz := HilbertCoordinates.energy V z
  let F0 := energy V (μ0,covarianceRoot S0)
  let B := 4/α*(C+|Fz|)+2*‖z‖^2
  let D := 4/α*(|F0|+|Fz|)+2*‖z‖^2
  let K := 2*B+2*D+1
  have ha := hV.alpha_pos
  have hb : 0 ≤ β := hV.alpha_pos.le.trans hV.alpha_le_beta
  have hC : 0 < C := by dsimp [C]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro N hN ω p X hpS hXS hS hpE hXE
  let Z := Sampling.initialEnvelope μ0 S0 N ω
  have hZ : 1 ≤ Z := LogEnergyLocalization.initialEnvelope_one_le μ0 S0 ω
  have hZ0 : 0 ≤ Z := le_trans zero_le_one hZ
  have hE := initialized_energy_bound hV μ0 S0 ω hS
  change energy V (Specification.cloudQ (Specification.gaussianCloud μ0 S0 N ω)) ≤ C*Z at hE
  apply iSup_le
  intro t
  have htp := t.property
  let qx := GaussianLocalization.rootState (empiricalMean (X t)) (empiricalCovariance (X t))
  let qp := GaussianLocalization.rootState (p.mean t) (p.cov t)
  have hqx : qx ∈ Domain d := by
    change (toModel d qx).2.PosDef
    rw [GaussianLocalization.toModel_rootState]
    exact (hXS t htp).posDef_sqrt
  have hqp : qp ∈ Domain d := by
    change (toModel d qp).2.PosDef
    rw [GaussianLocalization.toModel_rootState]
    exact (hpS t htp).posDef_sqrt
  have hqxe : HilbertCoordinates.energy V qx ≤ C*Z := by
    change energy V (toModel d qx) ≤ _
    rw [GaussianLocalization.toModel_rootState]
    exact (hXE t htp).trans hE
  have hqpe : HilbertCoordinates.energy V qp ≤ F0 := by
    change energy V (toModel d qp) ≤ _
    rw [GaussianLocalization.toModel_rootState]
    exact hpE t htp
  have hx := norm_sq_of_energy_trapping hV z qx hz hqx hcrit hqxe
  have hy := norm_sq_of_energy_trapping hV z qp hz hqp hcrit hqpe
  have hfour : 0 ≤ 4/α := by positivity
  change ‖qx‖^2 ≤ 4/α*(C*Z-Fz)+2*‖z‖^2 at hx
  change ‖qp‖^2 ≤ 4/α*(F0-Fz)+2*‖z‖^2 at hy
  have hnx : ‖qx‖^2 ≤ B*Z := by
    have hneg := mul_le_mul_of_nonneg_left (neg_le_abs Fz) hfour
    have hscale := mul_le_mul_of_nonneg_left hZ (by positivity : 0 ≤ 4/α*|Fz|+2*‖z‖^2)
    change ‖qx‖^2 ≤ (4/α*(C+|Fz|)+2*‖z‖^2)*Z
    nlinarith
  have hny : ‖qp‖^2 ≤ D := by
    have h := mul_le_mul_of_nonneg_left (add_le_add (le_abs_self F0) (neg_le_abs Fz)) hfour
    change ‖qp‖^2 ≤ 4/α*(|F0|+|Fz|)+2*‖z‖^2
    nlinarith
  have hcost := empirical_gaussian_moment_bound hN (X t) (p.mean t) (covarianceRoot (p.cov t))
  have hrootx := rootState_norm_sq (empiricalMean (X t)) (empiricalCovariance (X t)) (hXS t htp)
  have hrootp := rootState_norm_sq (p.mean t) (p.cov t) (hpS t htp)
  have htrace := GaussianLocalization.frobSq_sqrt_trace (p.cov t) (hpS t htp)
  change Specification.pathError X p t ≤ _
  apply hcost.trans
  apply ENNReal.ofReal_le_ofReal
  change 2*(‖empiricalMean (X t)‖^2+(empiricalCovariance (X t)).trace)+
    2*(‖p.mean t‖^2+frobSq (CFC.sqrt (p.cov t))) ≤ K*Z
  rw [htrace, ← hrootx, ← hrootp]
  change 2*‖qx‖^2+2*‖qp‖^2 ≤ K*Z
  have hdZ := mul_le_mul_of_nonneg_left hZ hD
  change 2*‖qx‖^2+2*‖qp‖^2 ≤ (2*B+2*D+1)*Z
  nlinarith


end Paper38.PathEnergyEnvelope
