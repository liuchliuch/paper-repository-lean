import Paper38.GaussianMomentMismatch
import Paper38.HighProbabilityShape
import Paper38.MomentEnergy
import Paper38.ExternalAnalyticInputs
import Paper38.DeterministicMain

/-! The source high-probability event is assembled from raw Gaussian
concentration and proved localization of the actual initialized moments. -/
noncomputable section
open MeasureTheory Set
open scoped Matrix MatrixOrder NNReal ENNReal
namespace Paper38.HighProbabilityMain
open Model HilbertCoordinates GaussianLocalization GaussianMomentMismatch
open Specification ExternalStatisticalInputs

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- Raw covariance full rank passes through the actual invertible initialization. -/
theorem gaussianCloud_covariance_posDef {N : ℕ} (hN : 0 < N)
    (μ0 : E d) (S0 : Mat d) (hS0 : S0.PosDef) (ω : Specification.Sample d N)
    (hraw : (Sampling.covariance d N ω).PosDef) :
    (empiricalCovariance (gaussianCloud μ0 S0 N ω)).PosDef := by
  change (empiricalCovariance (initialCloud μ0 (covarianceRoot S0) ω)).PosDef
  rw [(initial_moments hN μ0 (covarianceRoot S0) ω).2]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hraw.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_iff_isUnit.mpr hS0.posDef_sqrt.isUnit)

omit [NeZero d] in
/-- On the permitted tail-parameter interval the raw covariance defect is
uniformly bounded, so all high-probability initial states occupy one box. -/
lemma defect_uniform_bound (conc : Concentration d) {N : ℕ} (hN : 0 < N)
    (x : ℝ) (hxc : x ≤ conc.c0 * N) (ω : Specification.Sample d N)
    (hdef : Sampling.defect d N ω ≤ conc.C * (1+x) / N) :
    Sampling.defect d N ω ≤ conc.C * (1+conc.c0) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  apply hdef.trans
  apply (div_le_iff₀ hNr).mpr
  have h := mul_le_mul_of_nonneg_left (show 1+x ≤ (1+conc.c0)*(N:ℝ) by nlinarith)
    conc.C_pos.le
  nlinarith

/-- The common R is fixed before N and x. The event controls actual initialized
covariance, actual source energy, actual moment mismatch, and actual standardized
shape error; none of these controls is an external statistical input. -/
theorem localized_event {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (mom : CovarianceMoments d)
    (conc : Concentration d) (μ0 : E d) (S0 : Mat d) (hS0 : S0.PosDef)
    (qstar : Coordinates d) :
    ∃ R Ch ch c0 : ℝ, 0 ≤ R ∧ 0 < Ch ∧ 0 < ch ∧ 0 < c0 ∧
      (μ0,covarianceRoot S0) ∈ sublevel V qstar R ∧
      ∀ N : ℕ, d+1 ≤ N → ∀ x : ℝ, 1 ≤ x → x ≤ c0*N →
      ∃ H : Set (Specification.Sample d N), MeasurableSet H ∧
        sampleLaw d N Hᶜ ≤ ENNReal.ofReal (Ch*Real.exp (-ch*x)) ∧
        ∀ ω ∈ H, (Sampling.covariance d N ω).PosDef ∧
          (empiricalCovariance (gaussianCloud μ0 S0 N ω)).PosDef ∧
          cloudQ (gaussianCloud μ0 S0 N ω) ∈ sublevel V qstar R ∧
          coordinateSqDist (cloudQ (gaussianCloud μ0 S0 N ω)) (μ0,covarianceRoot S0) ≤
            (mismatchConstant (covarianceRoot S0)*conc.C) * (rate d N+x/N) ∧
          Sampling.shapeError d N ω ≤ ENNReal.ofReal (Ch*(rate d N+x/N)) := by
  let A := covarianceRoot S0
  have hA : A.PosDef := hS0.posDef_sqrt
  let M := conc.C*(1+conc.c0)
  have hM : 0 ≤ M := mul_nonneg conc.C_pos.le (by linarith [conc.c0_pos])
  obtain ⟨R,hR,hbox⟩ := exists_common_energy_sublevel hV μ0 A hA
    (Real.sqrt M) (1/2) (by norm_num) qstar
  have hpop : (μ0,A) ∈ sublevel V qstar R := by
    have h := hbox _ (population_mem_localizationBox μ0 A hA (Real.sqrt M) (1/2)
      (Real.sqrt_nonneg _) (by norm_num) (by norm_num))
    simpa only [toModel_rootState, sqrt_population_covariance A hA] using h
  obtain ⟨Ch,ch,c0,hCh,hch,hc0,hevent⟩ := HighProbabilityShape.standardized_event hV.dimension mom conc
  refine ⟨R,Ch,ch,min c0 conc.c0,hR,hCh,hch,lt_min hc0 conc.c0_pos,hpop,?_⟩
  intro N hN x hx hxc
  have hNp : 0 < N := lt_of_lt_of_le (Nat.succ_pos d) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have hxc1 : x ≤ c0*N := hxc.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hNr.le)
  have hxc2 : x ≤ conc.c0*N := hxc.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hNr.le)
  obtain ⟨H,hH,hP,hcontrol⟩ := hevent N hN x hx hxc1
  refine ⟨H,hH,hP,?_⟩
  intro ω hω
  rcases hcontrol ω hω with ⟨hraw,hdef,hOp,hshape⟩
  have hdefM : Sampling.defect d N ω ≤ M := defect_uniform_bound conc hNp x hxc2 ω hdef
  have hq := hbox _ (initial_state_localized_of_defect hNp μ0 A hA ω M hM hdefM hOp)
  have hδ : Sampling.defect d N ω ≤ conc.C*(rate d N+x/N) := by
    apply hdef.trans
    have heq : conc.C*(1+x)/(N:ℝ) = conc.C*((N:ℝ)⁻¹+x/N) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left
      (add_le_add_right (Model.inv_sampleSize_le_rate d N hV.dimension hNp) _) conc.C_pos.le
  refine ⟨hraw,gaussianCloud_covariance_posDef hNp μ0 S0 hS0 ω hraw,?_,?_,hshape⟩
  · simpa only [toModel_rootState, cloudQ, Model.covarianceRoot] using hq
  · exact (initial_moment_mismatch_of_opNorm hNp μ0 A hA ω (1/2)
      (by norm_num) (by norm_num) hOp).trans (by
        have h := mul_le_mul_of_nonneg_left hδ (mismatchConstant_pos A).le
        simpa only [mul_assoc] using h)

/-- Combining two actual path errors uses a genuine quadratic transport
triangle inequality and the physical-time supremum. -/
theorem last_iterate_pointwise {N : ℕ} (hN : 0 < N)
    (X : ParticlePath d N) (p : MomentPath d) (target : Measure (E d))
    [IsProbabilityMeasure target] (t : ℝ) (ht : 0 ≤ t)
    (A B : ℝ≥0∞) (hstat : pathSup X p ≤ A)
    (hmean : Transport.w2sq (p.law t) target ≤ B) :
    Transport.w2sq (empiricalLaw (X t)) target ≤ 2*A+2*B := by
  letI := AffineLifting.empiricalLaw_probability hN (X t)
  letI : IsProbabilityMeasure (p.law t) :=
    GaussianCoupling.gaussianLaw_probability (p.mean t) (covarianceRoot (p.cov t))
  have htime : pathError X p t ≤ pathSup X p :=
    le_iSup (fun s : {s : ℝ // 0 ≤ s} => pathError X p s) ⟨t,ht⟩
  exact (Transport.w2sq_triangle (empiricalLaw (X t)) (p.law t) target).trans
    (add_le_add (mul_le_mul_left' (htime.trans hstat) 2) (mul_le_mul_left' hmean 2))

/-- The logarithmic confidence parameter really lies in the admissible interval.
The lower confidence threshold has fixed constants and exponential N scaling. -/
lemma confidence_parameter (C c c0 K δ : ℝ) (N : ℕ)
    (hC : 0 < C) (hc : 0 < c) (hKC : C ≤ K) (hKe : Real.exp c ≤ K)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hlower : K*Real.exp (-(c*c0)*(N:ℝ)) ≤ δ) :
    let x := Real.log (K/δ)/c
    1 ≤ x ∧ x ≤ c0*N ∧ C*Real.exp (-c*x) ≤ δ := by
  have hK : 0 < K := hC.trans_le hKC
  have hr : 0 < K/δ := div_pos hK hδ
  have hlo : c ≤ Real.log (K/δ) := by
    apply (Real.le_log_iff_exp_le hr).mpr
    apply (le_div_iff₀ hδ).mpr
    exact (mul_le_of_le_one_right (Real.exp_nonneg _) hδ1).trans hKe
  have hexp : Real.exp (-(c*c0)*(N:ℝ))*Real.exp (c*c0*(N:ℝ)) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  have hhi : Real.log (K/δ) ≤ c*c0*N := by
    apply (Real.log_le_iff_le_exp hr).mpr
    apply (div_le_iff₀ hδ).mpr
    have hh : K ≤ δ*Real.exp (c*c0*(N:ℝ)) := calc
      K = K*(Real.exp (-(c*c0)*(N:ℝ))*Real.exp (c*c0*(N:ℝ))) := by rw [hexp,mul_one]
      _ = (K*Real.exp (-(c*c0)*(N:ℝ)))*Real.exp (c*c0*(N:ℝ)) := (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hlower (Real.exp_nonneg _)
    simpa only [mul_comm δ] using hh
  refine ⟨(le_div_iff₀ hc).mpr (by simpa using hlo),
    (div_le_iff₀ hc).mpr (by nlinarith), ?_⟩
  have he : -c*(Real.log (K/δ)/c) = -Real.log (K/δ) := by field_simp
  rw [he, Real.exp_neg, Real.exp_log hr, inv_div]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hK).mpr
  nlinarith [mul_le_mul_of_nonneg_right hKC hδ.le]

omit [NeZero d] in
/-- The population law cost is bounded by the exact source coordinate distance. -/
theorem population_w2sq_le_coordinate (p : MomentPath d) (qstar : Coordinates d) (t : ℝ) :
    Transport.w2sq (p.law t) (gaussianLaw qstar.1 qstar.2) ≤
      ENNReal.ofReal (coordinateSqDist (p.q t) qstar) :=
  GaussianCoupling.gaussian_w2sq_le (p.mean t) qstar.1 (covarianceRoot (p.cov t)) qstar.2

/-- Algebraic insertion of the initial-moment and standardized-shape bounds
into the proved deterministic transport oracle. -/
lemma oracle_rate_bound (S b M H u D : ℝ) (E : ℝ≥0∞)
    (hM : 0 ≤ M) (hH : 0 ≤ H) (hu : 0 ≤ u)
    (hD : D ≤ M*u) (hE : E ≤ ENNReal.ofReal (H*u)) :
    ENNReal.ofReal (2*S^2*D)+ENNReal.ofReal (2*b^2)*E ≤
      ENNReal.ofReal ((2*S^2*M+2*b^2*H)*u) := by
  calc
    _ ≤ ENNReal.ofReal (2*S^2*(M*u))+ENNReal.ofReal (2*b^2)*ENNReal.ofReal (H*u) :=
      add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hD (by positivity)))
        (mul_le_mul_left' hE _)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2*b^2),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- A single fixed coefficient absorbs the statistical and decaying terms. -/
lemma two_rate_bound (A D C u e : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hu : 0 ≤ u) (he : 0 ≤ e) (hCA : 2*A ≤ C) (hCD : 2*D ≤ C) :
    (2 : ℝ≥0∞)*ENNReal.ofReal (A*u)+2*ENNReal.ofReal (D*e) ≤
      ENNReal.ofReal (C*(u+e)) := by
  rw [← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [mul_le_mul_of_nonneg_right hCA hu, mul_le_mul_of_nonneg_right hCD he]

/-- Probability/event assembly from the own deterministic oracle and the own
population exponential estimate. The final source theorem supplies both analytic
premises; the external inputs here are only raw Gaussian concentration/moments. -/
theorem high_probability_of_oracle_and_decay (oracle : Specification.Theorem21)
    {V : E d → ℝ} {α β : ℝ} (hV : AdmissiblePotential V α β)
    (qstar : Coordinates d) (hstar : IsUniqueMinimizer V qstar)
    (mom : CovarianceMoments d) (conc : Concentration d)
    (μ0 : E d) (S0 : Mat d) (hS0 : S0.PosDef)
    (B κ : ℝ) (hB : 0 ≤ B) (hκ : 0 < κ)
    (hdecay : ∀ p : MomentPath d, IsMomentPathFrom V μ0 S0 p →
      ∀ t : ℝ, 0 ≤ t → coordinateSqDist (p.q t) qstar ≤ B*Real.exp (-2*κ*t)) :
    ∃ C c c0 : ℝ, 0 < C ∧ 0 < c ∧ 0 < c0 ∧
      ∀ N : ℕ, d+1 ≤ N →
      ∀ (p : MomentPath d) (X : Specification.Sample d N → ParticlePath d N),
        IsMomentPathFrom V μ0 S0 p →
        (∀ᵐ ω ∂sampleLaw d N, IsParticlePathFrom V (gaussianCloud μ0 S0 N ω) (X ω)) →
      ∀ x : ℝ, 1 ≤ x → x ≤ c0*N →
      ∃ H : Set (Specification.Sample d N), MeasurableSet H ∧
        sampleLaw d N Hᶜ ≤ ENNReal.ofReal (C*Real.exp (-c*x)) ∧
        ∀ ω ∈ H, pathSup (X ω) p ≤ ENNReal.ofReal (C*(rate d N+x/N)) ∧
          ∀ t : ℝ, 0 ≤ t →
          Transport.w2sq (empiricalLaw (X ω t)) (gaussianLaw qstar.1 qstar.2) ≤
            ENNReal.ofReal (C*(rate d N+x/N+Real.exp (-2*c*t))) := by
  obtain ⟨R,Ch,ch,c0,hR,hCh,hch,hc0,hpop,hevent⟩ :=
    localized_event hV mom conc μ0 S0 hS0 qstar
  obtain ⟨S,b,hS,hb,horacle⟩ := oracle d V α β hV qstar hstar R hR
  let M := mismatchConstant (covarianceRoot S0)*conc.C
  have hM : 0 ≤ M := mul_nonneg (mismatchConstant_pos _).le conc.C_pos.le
  let A := 2*S^2*M+2*b^2*Ch
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let C := 1+Ch+2*A+2*B
  have hC : 0 < C := by dsimp [C]; positivity
  have hCCh : Ch ≤ C := by dsimp [C]; linarith
  have hCA : 2*A ≤ C := by dsimp [C]; linarith
  have hCB : 2*B ≤ C := by dsimp [C]; linarith
  let c := min ch κ
  have hc : 0 < c := lt_min hch hκ
  refine ⟨C,c,c0,hC,hc,hc0,?_⟩
  intro N hN p X hp hX x hx hxc
  have hNp : 0 < N := lt_of_lt_of_le (Nat.succ_pos d) hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  let u := rate d N+x/N
  have hu : 0 ≤ u := add_nonneg (Model.rate_pos d N hV.dimension hNp).le (div_nonneg hx0 hNr.le)
  have hpq : p.q 0 = (μ0,covarianceRoot S0) := by simp only [MomentPath.q,hp.2.1,hp.2.2]
  obtain ⟨H0,hH0,hP0,hcontrol⟩ := hevent N hN x hx hxc
  obtain ⟨H1,hH1,hP1,hpath⟩ := ExpectedRates.measurable_core (sampleLaw d N)
    (fun ω => IsParticlePathFrom V (gaussianCloud μ0 S0 N ω) (X ω)) hX
  let H := H0 ∩ H1
  refine ⟨H,hH0.inter hH1,?_,?_⟩
  · calc
      sampleLaw d N Hᶜ ≤ sampleLaw d N H0ᶜ+sampleLaw d N H1ᶜ := by
        simpa only [H,compl_inter] using measure_union_le H0ᶜ H1ᶜ
      _ ≤ ENNReal.ofReal (Ch*Real.exp (-ch*x)) := by rw [hP1,add_zero]; exact hP0
      _ ≤ ENNReal.ofReal (C*Real.exp (-c*x)) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul hCCh (Real.exp_le_exp.mpr (by have := min_le_left ch κ; dsimp [c]; nlinarith))
          (Real.exp_nonneg _) hC.le
  · intro ω hω
    rcases hcontrol ω hω.1 with ⟨hraw,hcov,hqR,hmom,hshape⟩
    obtain ⟨_,_,horacleω⟩ := horacle N μ0 S0 (gaussianCloud μ0 S0 N ω)
      hNp hS0 hcov hpop hqR
    have hW := gaussianCloud_whitening hNp μ0 S0 hS0 ω hraw
    let W := (covarianceRoot (Sampling.covariance d N ω))⁻¹*(covarianceRoot S0)⁻¹
    have hbound := horacleω p (X ω) hp (hpath ω hω.2) W hW.1
    rw [hpq,hW.2] at hbound
    have hstat : pathSup (X ω) p ≤ ENNReal.ofReal (A*u) := by
      exact hbound.trans (oracle_rate_bound S b M Ch u _ _ hM hCh.le hu hmom hshape)
    refine ⟨hstat.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith : A ≤ C) hu)),?_⟩
    intro t ht
    have he : Real.exp (-2*κ*t) ≤ Real.exp (-2*c*t) :=
      Real.exp_le_exp.mpr (by have := min_le_right ch κ; dsimp [c]; nlinarith)
    have hmean : Transport.w2sq (p.law t) (gaussianLaw qstar.1 qstar.2) ≤
        ENNReal.ofReal (B*Real.exp (-2*c*t)) :=
      (population_w2sq_le_coordinate p qstar t).trans
        (ENNReal.ofReal_le_ofReal ((hdecay p hp t ht).trans (mul_le_mul_of_nonneg_left he hB)))
    letI := GaussianCoupling.gaussianLaw_probability qstar.1 qstar.2
    exact (last_iterate_pointwise hNp (X ω) p _ t ht _ _ hstat hmean).trans
      (two_rate_bound A B C u (Real.exp (-2*c*t)) hA hB hu (Real.exp_nonneg _) hCA hCB)

/-- The confidence formulation of the event bounds, including simultaneous
last-iterate control. The parameter transformation is proved above, rather than
assuming the statistical conclusion at logarithmic confidence. -/
theorem event_to_confidence {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ≥0∞) (g : Ω → ℝ → ℝ≥0∞)
    (N : ℕ) (hN : 0 < N) (r C c c0 K δ : ℝ)
    (hr : 0 ≤ r) (hC : 0 < C) (hc : 0 < c)
    (hKC : C ≤ K) (hKc : C/c ≤ K) (hKe : Real.exp c ≤ K)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hlower : K*Real.exp (-(c*c0)*(N:ℝ)) ≤ δ)
    (hevent : ∀ x : ℝ, 1 ≤ x → x ≤ c0*N →
      ∃ H : Set Ω, MeasurableSet H ∧ P Hᶜ ≤ ENNReal.ofReal (C*Real.exp (-c*x)) ∧
        ∀ ω ∈ H, f ω ≤ ENNReal.ofReal (C*(r+x/N)) ∧
          ∀ t : ℝ, 0 ≤ t → g ω t ≤ ENNReal.ofReal (C*(r+x/N+Real.exp (-2*c*t)))) :
    ∃ H : Set Ω, MeasurableSet H ∧ P Hᶜ ≤ ENNReal.ofReal δ ∧
      ∀ ω ∈ H, f ω ≤ ENNReal.ofReal (K*(r+Real.log (K/δ)/N)) ∧
        ∀ t : ℝ, 0 ≤ t →
        g ω t ≤ ENNReal.ofReal (K*(r+Real.log (K/δ)/N+Real.exp (-2*c*t))) := by
  let x := Real.log (K/δ)/c
  obtain ⟨hx,hxc,hδbound⟩ := confidence_parameter C c c0 K δ N hC hc hKC hKe hδ hδ1 hlower
  obtain ⟨H,hH,hP,hbound⟩ := hevent x hx hxc
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 ≤ Real.log (K/δ) := by
    have hlog := (le_div_iff₀ hc).mp hx
    linarith
  have hs : C*(r+x/N) ≤ K*(r+Real.log (K/δ)/N) := by
    have h1 := mul_le_mul_of_nonneg_right hKC hr
    have h2 := mul_le_mul_of_nonneg_right hKc (div_nonneg hL hNr.le)
    dsimp [x]
    nlinarith [show C*(Real.log (K/δ)/c/(N:ℝ)) =
      (C/c)*(Real.log (K/δ)/(N:ℝ)) by ring]
  refine ⟨H,hH,hP.trans (ENNReal.ofReal_le_ofReal hδbound),?_⟩
  intro ω hω
  refine ⟨((hbound ω hω).1).trans (ENNReal.ofReal_le_ofReal hs),?_⟩
  intro t ht
  apply ((hbound ω hω).2 t ht).trans
  apply ENNReal.ofReal_le_ofReal
  have he := mul_le_mul_of_nonneg_right hKC (Real.exp_nonneg (-2*c*t))
  nlinarith

omit [NeZero d] in
/-- The own energy/mobility geometry supplies one actual population coordinate
decay estimate for every source trajectory with the fixed initial moments. -/
theorem population_coordinate_decay
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    {V : E d → ℝ} {α β : ℝ} (hV : AdmissiblePotential V α β)
    (qstar : Coordinates d) (hstar : IsMinimizer V qstar)
    (μ0 : E d) (S0 : Mat d) (hS0 : S0.PosDef) :
    ∃ B κ : ℝ, 0 ≤ B ∧ 0 < κ ∧ ∀ p : MomentPath d,
      IsMomentPathFrom V μ0 S0 p → ∀ t : ℝ, 0 ≤ t →
        coordinateSqDist (p.q t) qstar ≤ B*Real.exp (-2*κ*t) := by
  let R := max 0 (Model.energy V (μ0,covarianceRoot S0)-Model.energy V qstar)
  obtain ⟨B,hB,κ,hκ,hdecay⟩ := MomentEnergy.uniform_decay stein sqrt hV qstar hstar R (le_max_left _ _)
  refine ⟨B,κ,hB,hκ,?_⟩
  intro p hp t ht
  have hpq : p.q 0 = (μ0,covarianceRoot S0) := by simp only [MomentPath.q,hp.2.1,hp.2.2]
  have hR : p.q 0 ∈ sublevel V qstar R := by
    rw [hpq]
    exact ⟨hS0.posDef_sqrt,le_max_right _ _⟩
  exact (hdecay p hp.1 hR t ht).2

omit [NeZero d] in
/-- The exact Gaussian population Wasserstein estimate used by both source
last-iterate conclusions, derived from the proved coordinate energy decay. -/
theorem population_gaussian_decay
    (stein : ExternalGaussianAnalysis.GaussianSteinTheorem d)
    (sqrt : ExternalMatrixAnalysis.PrincipalRootDifferentiation d)
    {V : E d → ℝ} {α β : ℝ} (hV : AdmissiblePotential V α β)
    (qstar : Coordinates d) (hstar : IsMinimizer V qstar)
    (μ0 : E d) (S0 : Mat d) (hS0 : S0.PosDef) :
    ∃ B κ : ℝ, 0 ≤ B ∧ 0 < κ ∧ ∀ p : MomentPath d,
      IsMomentPathFrom V μ0 S0 p → ∀ t : ℝ, 0 ≤ t →
        Transport.w2sq (p.law t) (gaussianLaw qstar.1 qstar.2) ≤
          ENNReal.ofReal (B*Real.exp (-2*κ*t)) := by
  obtain ⟨B,κ,hB,hκ,hdecay⟩ := population_coordinate_decay stein sqrt hV qstar hstar μ0 S0 hS0
  refine ⟨B,κ,hB,hκ,?_⟩
  intro p hp t ht
  exact (population_w2sq_le_coordinate p qstar t).trans
    (ENNReal.ofReal_le_ofReal (hdecay p hp t ht))

/-- The literal source high-probability specification after the own population
energy theorem has discharged the decay premise. The final analytic assembly
supplies the independently proved deterministic oracle. -/
theorem theorem24_of_oracle (oracle : Specification.Theorem21)
    (extern : ∀ d : ℕ, ExternalAnalyticInputs.Baselines d)
    (mom : ∀ d : ℕ, 1 ≤ d → CovarianceMoments d) (conc : ∀ d : ℕ, 1 ≤ d → Concentration d) :
    Specification.Theorem24 := by
  intro d V α β hV qstar hstar μ0 S0 hS0
  letI : NeZero d := ⟨by have := hV.dimension; omega⟩
  obtain ⟨B,κ,hB,hκ,hdecay⟩ := population_coordinate_decay (extern d).stein (extern d).sqrt
    hV qstar hstar.1 μ0 S0 hS0
  exact high_probability_of_oracle_and_decay oracle hV qstar hstar (mom d hV.dimension) (conc d hV.dimension)
    μ0 S0 hS0 B κ hB hκ hdecay

/-- The final confidence reformulation in the source Theorem 2.4, with fixed
constants before N and confidence δ. The same event controls every time. -/
theorem confidence_of_oracle (oracle : Specification.Theorem21)
    (extern : ∀ d : ℕ, ExternalAnalyticInputs.Baselines d)
    (mom : ∀ d : ℕ, 1 ≤ d → CovarianceMoments d) (conc : ∀ d : ℕ, 1 ≤ d → Concentration d)
    (d : ℕ) (V : E d → ℝ) (α β : ℝ) (hV : AdmissiblePotential V α β)
    (qstar : Coordinates d) (hstar : IsUniqueMinimizer V qstar)
    (μ0 : E d) (S0 : Mat d) (hS0 : S0.PosDef) :
    ∃ K a : ℝ, 0 < K ∧ 0 < a ∧ ∀ N : ℕ, d+1 ≤ N →
      ∀ (p : MomentPath d) (X : Specification.Sample d N → ParticlePath d N),
        IsMomentPathFrom V μ0 S0 p →
        (∀ᵐ ω ∂sampleLaw d N, IsParticlePathFrom V (gaussianCloud μ0 S0 N ω) (X ω)) →
      ∀ δ : ℝ, K*Real.exp (-a*N) ≤ δ → δ ≤ 1/2 →
      ∃ H : Set (Specification.Sample d N), MeasurableSet H ∧
        sampleLaw d N Hᶜ ≤ ENNReal.ofReal δ ∧
        ∀ ω ∈ H, pathSup (X ω) p ≤ ENNReal.ofReal (K*(rate d N+Real.log (K/δ)/N)) ∧
          ∀ t : ℝ, 0 ≤ t →
          Transport.w2sq (empiricalLaw (X ω t)) (gaussianLaw qstar.1 qstar.2) ≤
            ENNReal.ofReal (K*(rate d N+Real.log (K/δ)/N+Real.exp (-2*a*t))) := by
  obtain ⟨C,c,c0,hC,hc,hc0,hevent⟩ :=
    theorem24_of_oracle oracle extern mom conc d V α β hV qstar hstar μ0 S0 hS0
  let K := 1+C+C/c+Real.exp c
  have hCc : 0 ≤ C/c := div_nonneg hC.le hc.le
  have hK : 0 < K := by dsimp [K]; positivity
  have hKC : C ≤ K := by dsimp [K]; linarith [Real.exp_pos c]
  have hKc : C/c ≤ K := by dsimp [K]; linarith [Real.exp_pos c]
  have hKe : Real.exp c ≤ K := by dsimp [K]; linarith
  let a := min c (c*c0)
  have ha : 0 < a := lt_min hc (mul_pos hc hc0)
  refine ⟨K,a,hK,ha,?_⟩
  intro N hN p X hp hX δ hδlower hδhalf
  have hNp : 0 < N := lt_of_lt_of_le (Nat.succ_pos d) hN
  have hNr : (0 : ℝ) ≤ N := by positivity
  have hδ : 0 < δ := (mul_pos hK (Real.exp_pos _)).trans_le hδlower
  have hδ1 : δ ≤ 1 := by linarith
  have hlower : K*Real.exp (-(c*c0)*(N:ℝ)) ≤ δ := by
    apply le_trans _ hδlower
    apply mul_le_mul_of_nonneg_left _ hK.le
    apply Real.exp_le_exp.mpr
    have h := min_le_right c (c*c0)
    dsimp [a]
    nlinarith
  obtain ⟨H,hH,hP,hbound⟩ := event_to_confidence (sampleLaw d N)
    (fun ω => pathSup (X ω) p)
    (fun ω t => Transport.w2sq (empiricalLaw (X ω t)) (gaussianLaw qstar.1 qstar.2))
    N hNp (rate d N) C c c0 K δ (Model.rate_pos d N hV.dimension hNp).le
    hC hc hKC hKc hKe hδ hδ1 hlower (hevent N hN p X hp hX)
  refine ⟨H,hH,hP,?_⟩
  intro ω hω
  refine ⟨(hbound ω hω).1,?_⟩
  intro t ht
  apply ((hbound ω hω).2 t ht).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ hK.le
  apply add_le_add_left
  apply Real.exp_le_exp.mpr
  have h := min_le_left c (c*c0)
  dsimp [a]
  nlinarith

/-- Exact source contract with the user-retained ordinary baseline bundles.
The final source assembly supplies `oracle` from its independent analytic proof. -/
theorem theorem24_with_baselines (oracle : Specification.Theorem21)
    (extern : ∀ d : ℕ, ExternalAnalyticInputs.Baselines d)
    (stats : ∀ d : ℕ, 1 ≤ d → ExternalStatisticalInputs.Baselines d) :
    Specification.Theorem24 :=
  theorem24_of_oracle oracle extern (fun d hd => (stats d hd).covariance)
    (fun d hd => (stats d hd).concentration)

/-- Bundled form of the complete logarithmic-confidence consequence. -/
theorem confidence_with_baselines (oracle : Specification.Theorem21)
    (extern : ∀ d : ℕ, ExternalAnalyticInputs.Baselines d)
    (stats : ∀ d : ℕ, 1 ≤ d → ExternalStatisticalInputs.Baselines d)
    (d : ℕ) (V : E d → ℝ) (α β : ℝ) (hV : AdmissiblePotential V α β)
    (qstar : Coordinates d) (hstar : IsUniqueMinimizer V qstar)
    (μ0 : E d) (S0 : Mat d) (hS0 : S0.PosDef) :
    ∃ K a : ℝ, 0 < K ∧ 0 < a ∧ ∀ N : ℕ, d+1 ≤ N →
      ∀ (p : MomentPath d) (X : Specification.Sample d N → ParticlePath d N),
        IsMomentPathFrom V μ0 S0 p →
        (∀ᵐ ω ∂sampleLaw d N, IsParticlePathFrom V (gaussianCloud μ0 S0 N ω) (X ω)) →
      ∀ δ : ℝ, K*Real.exp (-a*N) ≤ δ → δ ≤ 1/2 →
      ∃ H : Set (Specification.Sample d N), MeasurableSet H ∧
        sampleLaw d N Hᶜ ≤ ENNReal.ofReal δ ∧
        ∀ ω ∈ H, pathSup (X ω) p ≤ ENNReal.ofReal (K*(rate d N+Real.log (K/δ)/N)) ∧
          ∀ t : ℝ, 0 ≤ t →
          Transport.w2sq (empiricalLaw (X ω t)) (gaussianLaw qstar.1 qstar.2) ≤
            ENNReal.ofReal (K*(rate d N+Real.log (K/δ)/N+Real.exp (-2*a*t))) :=
  confidence_of_oracle oracle extern (fun d hd => (stats d hd).covariance)
    (fun d hd => (stats d hd).concentration) d V α β hV qstar hstar μ0 S0 hS0

/-- Complete literal source Theorem 2.4: every own analytic premise is now
proved, leaving only the named standard analytic and raw statistical baselines. -/
theorem theorem24
    (extern : ∀ d : ℕ, ExternalAnalyticInputs.Baselines d)
    (stats : ∀ d : ℕ, 1 ≤ d → ExternalStatisticalInputs.Baselines d) :
    Specification.Theorem24 :=
  theorem24_with_baselines (DeterministicMain.theorem21 extern) extern stats

/-- Complete source logarithmic-confidence consequence, with the deterministic
oracle discharged by its actual independent proof. -/
theorem theorem24_confidence
    (extern : ∀ d : ℕ, ExternalAnalyticInputs.Baselines d)
    (stats : ∀ d : ℕ, 1 ≤ d → ExternalStatisticalInputs.Baselines d)
    (d : ℕ) (V : E d → ℝ) (α β : ℝ) (hV : AdmissiblePotential V α β)
    (qstar : Coordinates d) (hstar : IsUniqueMinimizer V qstar)
    (μ0 : E d) (S0 : Mat d) (hS0 : S0.PosDef) :
    ∃ K a : ℝ, 0 < K ∧ 0 < a ∧ ∀ N : ℕ, d+1 ≤ N →
      ∀ (p : MomentPath d) (X : Specification.Sample d N → ParticlePath d N),
        IsMomentPathFrom V μ0 S0 p →
        (∀ᵐ ω ∂sampleLaw d N, IsParticlePathFrom V (gaussianCloud μ0 S0 N ω) (X ω)) →
      ∀ δ : ℝ, K*Real.exp (-a*N) ≤ δ → δ ≤ 1/2 →
      ∃ H : Set (Specification.Sample d N), MeasurableSet H ∧
        sampleLaw d N Hᶜ ≤ ENNReal.ofReal δ ∧
        ∀ ω ∈ H, pathSup (X ω) p ≤ ENNReal.ofReal (K*(rate d N+Real.log (K/δ)/N)) ∧
          ∀ t : ℝ, 0 ≤ t →
          Transport.w2sq (empiricalLaw (X ω t)) (gaussianLaw qstar.1 qstar.2) ≤
            ENNReal.ofReal (K*(rate d N+Real.log (K/δ)/N+Real.exp (-2*a*t))) :=
  confidence_with_baselines (DeterministicMain.theorem21 extern) extern stats
    d V α β hV qstar hstar μ0 S0 hS0


end Paper38.HighProbabilityMain
