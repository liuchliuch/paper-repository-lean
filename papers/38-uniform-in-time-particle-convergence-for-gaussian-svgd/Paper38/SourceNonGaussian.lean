import Paper38.SourceParticleLimit
import Paper38.PathEnergyEnvelope
import Paper38.SourceAffine
import Paper38.NonGaussianInitialization
import Paper38.NonGaussianWhitening

/-! Source Corollary 2.7. The ordinary raw empirical W₂/mean/covariance strong
laws and zero-cost separation are explicit external inputs. Whitening
continuity, finite-cloud limits, all-count full rank, spectral comparison and
non-Gaussian positivity are own derivations. -/

noncomputable section
universe u
namespace Paper38.SourceNonGaussian

open Paper38.Model Paper38.Transport Paper38.AffineLifting Paper38.ParticleLimit
open Paper38.ExternalEmpiricalTransport Paper38.NonGaussianInitialization
open MeasureTheory Set Filter
open scoped BigOperators Matrix MatrixOrder ENNReal NNReal Topology

variable {d N : ℕ}

/-- A limiting cloud belongs to the original physical-time particle dynamics. -/
def IsLimitingCloud (V : E d → ℝ) (x y : Fin N → E d) : Prop :=
  ∃ X : Specification.ParticlePath d N, Specification.IsParticlePathFrom V x X ∧
    ∀ i, Tendsto (fun t => X t i) atTop (𝓝 (y i))

/-- The limiting cloud and its two fixed-covariance spectral bounds. This is a
result predicate, never an external input or a field of a baseline theorem. -/
def HasLimitWithFloor [NeZero d] (V : E d → ℝ) (qstar : Coordinates d)
    (x y : Fin N → E d) : Prop :=
  IsLimitingCloud V x y ∧
  (covarianceMin qstar.2 : ℝ≥0∞) *
    w2sq (empiricalLaw (standardizedCloud x (covarianceRoot (empiricalCovariance x))⁻¹))
      (standardGaussian d) ≤ w2sq (empiricalLaw y) (gaussianLaw qstar.1 qstar.2) ∧
  w2sq (empiricalLaw y) (gaussianLaw qstar.1 qstar.2) ≤
    (covarianceMax qstar.2 : ℝ≥0∞) *
    w2sq (empiricalLaw (standardizedCloud x (covarianceRoot (empiricalCovariance x))⁻¹))
      (standardGaussian d)

/-- Every full-rank cloud has an actual limiting cloud. Its energy is finite,
so the own Proposition 2.6 applies on a suitable cloud-dependent sublevel;
the resulting spectral comparison is independent of that sublevel. -/
theorem finite_limit_with_floor [NeZero d]
    (extern : ExternalAnalyticInputs.Baselines d)
    {V : E d → ℝ} {α β : ℝ} (hV : AdmissiblePotential V α β)
    (qstar : Coordinates d) (hstar : Specification.IsMinimizer V qstar)
    (hN : 0 < N) (x : Fin N → E d) (hS : (empiricalCovariance x).PosDef) :
    ∃ y : Fin N → E d, HasLimitWithFloor V qstar x y := by
  let R := max 1 (Model.energy V (Specification.cloudQ x) - Model.energy V qstar)
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hi : Specification.cloudQ x ∈ sublevel V qstar R :=
    ⟨hS.posDef_sqrt, le_max_right _ _⟩
  obtain ⟨C, hC, decay, hd, hmain⟩ := SourceParticleLimit.proposition26_at
    extern.stein extern.sqrt extern.decayingFundamental hV qstar hstar R hR.le
  obtain ⟨X, hX, huniq⟩ := SourceFlowMeasurability.particleWellPosed extern hV hN x hS
  have hiX : Specification.cloudQ (X 0) ∈ sublevel V qstar R := by rwa [hX.2]
  let W := (covarianceRoot (empiricalCovariance x))⁻¹
  have hW : IsWhitening (X 0) W := by
    rw [hX.2]
    exact SourceAffine.principal_whitening x hS
  obtain ⟨Linf, hLinf, B, y, hunit, hcov, hcenter, haffine, hrate,
    hXlim, herror, hfloor, hpositive⟩ := hmain N hN X hX.1 hiX W hW
  have ha := covarianceMin_eq_of_covariance B qstar.2 hcov
  have hb := covarianceMax_eq_of_covariance B qstar.2 hcov
  refine ⟨y, ⟨⟨X, hX, hXlim⟩, ?_⟩⟩
  simpa only [ha, hb, hX.2, W] using hfloor

/-- A fixed choice is harmless because the actual particle trajectory and its
coordinatewise limit are unique. Outside the full-rank event a zero cloud is
used only to make this function total. -/
def chosenLimitCloud [NeZero d] (V : E d → ℝ) (qstar : Coordinates d)
    (x : Fin N → E d) : Fin N → E d := by
  classical
  exact if h : ∃ y, HasLimitWithFloor V qstar x y then Classical.choose h else 0

theorem chosenLimitCloud_spec [NeZero d] {V : E d → ℝ} {qstar : Coordinates d}
    {x : Fin N → E d} (h : ∃ y, HasLimitWithFloor V qstar x y) :
    HasLimitWithFloor V qstar x (chosenLimitCloud V qstar x) := by
  rw [chosenLimitCloud, dif_pos h]
  exact Classical.choose_spec h

/-- Any other actual limiting cloud gives exactly the same empirical law. -/
theorem limitingCloud_unique [NeZero d]
    (extern : ExternalAnalyticInputs.Baselines d)
    {V : E d → ℝ} {α β : ℝ} (hV : AdmissiblePotential V α β)
    (hN : 0 < N) (x y z : Fin N → E d) (hS : (empiricalCovariance x).PosDef)
    (hy : IsLimitingCloud V x y) (hz : IsLimitingCloud V x z) : y = z := by
  obtain ⟨X, hX, hXlim⟩ := hy
  obtain ⟨Y, hY, hYlim⟩ := hz
  obtain ⟨Z, hZ, huniq⟩ := SourceFlowMeasurability.particleWellPosed extern hV hN x hS
  have hpaths (t : ℝ) (ht : 0 ≤ t) : X t = Y t :=
    (huniq X hX t ht).trans (huniq Y hY t ht).symm
  funext i
  apply tendsto_nhds_unique (hXlim i)
  apply (hYlim i).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact congrFun (hpaths t ht).symm i

/-- The population standardized law in the source statement. -/
def populationShape (ν : Measure (E d)) : Measure (E d) :=
  ν.map (fun y => matVec (covarianceRoot (populationCovariance ν))⁻¹ (y-populationMean ν))

instance populationShape_probability (ν : Measure (E d)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (populationShape ν) :=
  Measure.isProbabilityMeasure_map
    (((GaussianAffine.continuous_matVec _).comp (continuous_id.sub continuous_const)).measurable.aemeasurable)

/-- The finite-second-moment raw strong law also proves that the population
shape defect is a finite transport cost. Choose one sample path on its
probability-one convergence event and one finite count with small transport
cost to the population shape; the own finite empirical--Gaussian moment bound
and the genuine transport triangle finish the argument. No new external
transport-finiteness theorem is used. -/
theorem populationShape_cost_lt_top [NeZero d] {Ω : Type*} [MeasurableSpace Ω]
    (stronglaws : RawEmpiricalStrongLaws Ω d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure (E d)) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → E d) (hmeas : ∀ n, Measurable (X n))
    (hindep : ProbabilityTheory.iIndepFun X P) (hlaw : ∀ n, Measure.map (X n) P = ν)
    (hsecond : Integrable (fun x : E d => ‖x‖ ^ 2) ν)
    (hSigma : (populationCovariance ν).PosDef) :
    w2sq (populationShape ν) (standardGaussian d) < ⊤ := by
  obtain ⟨ω, hω⟩ := (ae_standardized_empirical_tendsto stronglaws sqrt P ν X
    hmeas hindep hlaw hsecond hSigma).exists
  have hevent : ∀ᶠ n in atTop, w2sq
      (empiricalLaw (standardizedCloud (fun i : Fin (n+1) => X i ω)
        (covarianceRoot (empiricalCovariance (fun i : Fin (n+1) => X i ω)))⁻¹))
      (populationShape ν) < 1 :=
    hω.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  obtain ⟨n, hn⟩ := hevent.exists
  let z := standardizedCloud (fun i : Fin (n+1) => X i ω)
    (covarianceRoot (empiricalCovariance (fun i : Fin (n+1) => X i ω)))⁻¹
  letI := AffineLifting.empiricalLaw_probability (Nat.succ_pos n) z
  letI := GaussianAffine.standardGaussian_probability d
  have hgap : w2sq (populationShape ν) (empiricalLaw z) < ⊤ := by
    rw [w2sq_comm]
    exact hn.trans (by simp)
  have hident : gaussianLaw (0 : E d) (1 : Mat d) = standardGaussian d := by
    unfold gaussianLaw
    have hf : (fun z : E d => (0 : E d) + matVec (1 : Mat d) z) = id := by
      funext z
      simp [matVec, vec]
    rw [hf, Measure.map_id]
  have hgauss : w2sq (empiricalLaw z) (standardGaussian d) < ⊤ := by
    have hb := PathEnergyEnvelope.empirical_gaussian_moment_bound (Nat.succ_pos n) z (0 : E d) (1 : Mat d)
    rw [hident] at hb
    exact hb.trans_lt ENNReal.ofReal_lt_top
  apply (w2sq_triangle (populationShape ν) (empiricalLaw z) (standardGaussian d)).trans_lt
  exact ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top (by norm_num) hgap, ENNReal.mul_lt_top (by norm_num) hgauss⟩

/-- The complete almost-sure spectral comparison (2.21) for the actual chosen
limiting clouds; the full-rank and strong-law events are on the same space. -/
theorem corollary27_at [NeZero d] {Ω : Type*} [MeasurableSpace Ω]
    (extern : ExternalAnalyticInputs.Baselines d)
    (stronglaws : RawEmpiricalStrongLaws Ω d) (separation : QuadraticTransportSeparation d)
    {V : E d → ℝ} {α β : ℝ} (hV : AdmissiblePotential V α β)
    (qstar : Coordinates d) (hstar : Specification.IsMinimizer V qstar)
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure (E d)) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → E d) (hmeas : ∀ n, Measurable (X n))
    (hindep : ProbabilityTheory.iIndepFun X P) (hlaw : ∀ n, Measure.map (X n) P = ν)
    (hdensity : ν ≪ volume) (hsecond : Integrable (fun x : E d => ‖x‖ ^ 2) ν)
    (hSigma : (populationCovariance ν).PosDef)
    (hnon : ν ≠ gaussianLaw (populationMean ν) (covarianceRoot (populationCovariance ν))) :
    0 < w2sq (populationShape ν) (standardGaussian d) ∧
    ∀ᵐ ω ∂P,
      (∀ n, d ≤ n → IsLimitingCloud V (fun i : Fin (n+1) => X i ω)
        (chosenLimitCloud V qstar (fun i : Fin (n+1) => X i ω))) ∧
      (covarianceMin qstar.2 : ℝ≥0∞) * w2sq (populationShape ν) (standardGaussian d) ≤
        liminf (fun n => w2sq
          (empiricalLaw (chosenLimitCloud V qstar (fun i : Fin (n+1) => X i ω)))
          (gaussianLaw qstar.1 qstar.2)) atTop ∧
      liminf (fun n => w2sq
          (empiricalLaw (chosenLimitCloud V qstar (fun i : Fin (n+1) => X i ω)))
          (gaussianLaw qstar.1 qstar.2)) atTop ≤
        limsup (fun n => w2sq
          (empiricalLaw (chosenLimitCloud V qstar (fun i : Fin (n+1) => X i ω)))
          (gaussianLaw qstar.1 qstar.2)) atTop ∧
      limsup (fun n => w2sq
          (empiricalLaw (chosenLimitCloud V qstar (fun i : Fin (n+1) => X i ω)))
          (gaussianLaw qstar.1 qstar.2)) atTop ≤
        (covarianceMax qstar.2 : ℝ≥0∞) * w2sq (populationShape ν) (standardGaussian d) := by
  refine ⟨NonGaussianWhitening.population_whitened_cost_pos separation ν hSigma hnon, ?_⟩
  have hfull := NonGaussianWhitening.ae_iid_empiricalCovariance_posDef_succ_all
    P ν hdensity X hmeas hindep hlaw
  have hshape := ae_standardized_empirical_tendsto stronglaws extern.sqrt P ν X
    hmeas hindep hlaw hsecond hSigma
  filter_upwards [hfull, hshape] with ω hfullω hshapeω
  have hspec (n : ℕ) (hn : d ≤ n) : HasLimitWithFloor V qstar
      (fun i : Fin (n+1) => X i ω) (chosenLimitCloud V qstar (fun i : Fin (n+1) => X i ω)) :=
    chosenLimitCloud_spec (finite_limit_with_floor extern hV qstar hstar (Nat.succ_pos n)
      _ (hfullω n hn))
  have hshapeCost := standardized_shape_error_tendsto ν
    (fun n => standardizedCloud (fun i : Fin (n+1) => X i ω)
      (covarianceRoot (empiricalCovariance (fun i : Fin (n+1) => X i ω)))⁻¹)
    (populationShape ν) hshapeω
  have hlimits := spectral_liminf_limsup _ _ _ (covarianceMin qstar.2) (covarianceMax qstar.2)
    hshapeCost ((eventually_ge_atTop d).mono (fun n hn => (hspec n hn).2.1))
    ((eventually_ge_atTop d).mono (fun n hn => (hspec n hn).2.2))
  exact ⟨fun n hn => (hspec n hn).1, hlimits⟩

end Paper38.SourceNonGaussian

namespace Paper38.Production
open Paper38.Model Paper38.Transport Paper38.AffineLifting Paper38.SourceNonGaussian
open Paper38.ExternalEmpiricalTransport MeasureTheory Set Filter
open scoped ENNReal Topology

/-- Literal source Corollary 2.7 on one common i.i.d. probability space. The
positive-count index n+1 is exactly N; deleting finitely many N<d+1 leaves its
lower/upper limits and isotropic convergence unchanged. -/
def Specification27 : Prop :=
  ∀ (d : ℕ) [NeZero d] (V : E d → ℝ) (α β : ℝ), AdmissiblePotential V α β →
  ∀ qstar, Specification.IsUniqueMinimizer V qstar →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure (E d)) [IsProbabilityMeasure ν] (X : ℕ → Ω → E d),
    (∀ n, Measurable (X n)) → ProbabilityTheory.iIndepFun X P →
    (∀ n, Measure.map (X n) P = ν) → ν ≪ volume →
    Integrable (fun x : E d => ‖x‖ ^ 2) ν → (populationCovariance ν).PosDef →
    ν ≠ gaussianLaw (populationMean ν) (covarianceRoot (populationCovariance ν)) →
    0 < w2 (populationShape ν) (standardGaussian d) ∧
    w2 (populationShape ν) (standardGaussian d) < ⊤ ∧
    0 < w2sq (populationShape ν) (standardGaussian d) ∧
    w2sq (populationShape ν) (standardGaussian d) < ⊤ ∧
    ∀ᵐ ω ∂P,
      (∀ n, d ≤ n → IsLimitingCloud V (fun i : Fin (n+1) => X i ω)
        (chosenLimitCloud V qstar (fun i : Fin (n+1) => X i ω))) ∧
      (covarianceMin qstar.2 : ℝ≥0∞) * w2sq (populationShape ν) (standardGaussian d) ≤
        liminf (fun n => w2sq
          (empiricalLaw (chosenLimitCloud V qstar (fun i : Fin (n+1) => X i ω)))
          (gaussianLaw qstar.1 qstar.2)) atTop ∧
      liminf (fun n => w2sq
          (empiricalLaw (chosenLimitCloud V qstar (fun i : Fin (n+1) => X i ω)))
          (gaussianLaw qstar.1 qstar.2)) atTop ≤
        limsup (fun n => w2sq
          (empiricalLaw (chosenLimitCloud V qstar (fun i : Fin (n+1) => X i ω)))
          (gaussianLaw qstar.1 qstar.2)) atTop ∧
      limsup (fun n => w2sq
          (empiricalLaw (chosenLimitCloud V qstar (fun i : Fin (n+1) => X i ω)))
          (gaussianLaw qstar.1 qstar.2)) atTop ≤
        (covarianceMax qstar.2 : ℝ≥0∞) * w2sq (populationShape ν) (standardGaussian d) ∧
      0 < liminf (fun n => w2sq
          (empiricalLaw (chosenLimitCloud V qstar (fun i : Fin (n+1) => X i ω)))
          (gaussianLaw qstar.1 qstar.2)) atTop ∧
      (∀ σ : ℝ, qstar.2 * qstar.2.transpose = σ ^ 2 • (1 : Mat d) →
        Tendsto (fun n => w2sq
          (empiricalLaw (chosenLimitCloud V qstar (fun i : Fin (n+1) => X i ω)))
          (gaussianLaw qstar.1 qstar.2)) atTop
          (𝓝 (ENNReal.ofReal (σ ^ 2) * w2sq (populationShape ν) (standardGaussian d))))

end Paper38.Production

namespace Paper38.SourceNonGaussian
open Paper38.Model Paper38.Transport Paper38.AffineLifting Paper38.ParticleLimit
open Paper38.ExternalEmpiricalTransport MeasureTheory Set Filter
open scoped ENNReal Topology

/-- Complete Corollary 2.7, with only precisely isolated standard raw strong
laws and optimal-transport separation in addition to the ordinary analysis
baselines. In particular no whitening or spectral floor is assumed. -/
theorem corollary27 (extern : ∀ d : ℕ, ExternalAnalyticInputs.Baselines d)
    (stronglaws : ∀ (Ω : Type u) [MeasurableSpace Ω] (d : ℕ), RawEmpiricalStrongLaws Ω d)
    (separation : ∀ d : ℕ, QuadraticTransportSeparation d) : Production.Specification27.{u} := by
  intro d inst V α β hV qstar hstar Ω mΩ P hP ν hν X hmeas hindep hlaw hdensity hsecond hSigma hnon
  obtain ⟨hD, hmain⟩ := corollary27_at (extern d) (stronglaws Ω d) (separation d)
    hV qstar hstar.1 P ν X hmeas hindep hlaw hdensity hsecond hSigma hnon
  have hfinite := populationShape_cost_lt_top (stronglaws Ω d) (extern d).sqrt P ν X
    hmeas hindep hlaw hsecond hSigma
  have hW2finite : w2 (populationShape ν) (standardGaussian d) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfinite.ne
  refine ⟨ENNReal.rpow_pos_of_nonneg hD (by norm_num), hW2finite, hD, hfinite, ?_⟩
  filter_upwards [hmain] with ω hω
  have hmin : (0 : ℝ≥0∞) < covarianceMin qstar.2 := by
    exact_mod_cast covarianceMin_pos qstar.2 hstar.1.1.isUnit
  have hpositive := (ENNReal.mul_pos hmin.ne' hD.ne').trans_le hω.2.1
  refine ⟨hω.1, hω.2.1, hω.2.2.1, hω.2.2.2, hpositive, ?_⟩
  intro σ hSigmaIso
  have hiso := NonGaussianWhitening.isotropic_spectral_factors qstar.2 σ hSigmaIso
  have ha : (covarianceMin qstar.2 : ℝ≥0∞) = ENNReal.ofReal (σ ^ 2) := by
    rw [← ENNReal.ofReal_coe_nnreal, hiso.1]
  have hb : (covarianceMax qstar.2 : ℝ≥0∞) = ENNReal.ofReal (σ ^ 2) := by
    rw [← ENNReal.ofReal_coe_nnreal, hiso.2]
  exact tendsto_of_le_liminf_of_limsup_le
    (by simpa only [ha] using hω.2.1) (by simpa only [hb] using hω.2.2.2)

end Paper38.SourceNonGaussian
