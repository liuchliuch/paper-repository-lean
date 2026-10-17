import Paper26.GraphFamily
import Paper26.HaarLossBalls
import Paper26.VolumeNormalizerUpper
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Local graph-chart volume transfer

The operator norm below is the norm of the actual rectangular map between
Euclidean complex spaces. The chart metric and density are the genuine
matrix objects in `GraphFamily`. The only graph-chart distribution input
is the known invariant-volume density on arbitrary measurable parameter
sets; it does not contain a successful-loss bound.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.ChartVolume

open QuantumModel HaarFrames HaarTruncation

local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

local instance matrixBorelSpace (m n : Type*) [Fintype m] [Fintype n] :
    BorelSpace (Matrix m n ℂ) := inferInstanceAs (BorelSpace (m → n → ℂ))

variable {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ] [DecidableEq σ]

/-- Rectangular version of `Matrix.toEuclideanCLM`: the actual complex
matrix map between the two finite Euclidean Hilbert spaces. -/
def operator (X : Matrix σ κ ℂ) : EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ σ :=
  (Matrix.toEuclideanLin X).toContinuousLinearMap

omit [DecidableEq σ] in
@[simp] theorem operator_apply (X : Matrix σ κ ℂ) (v : EuclideanSpace ℂ κ) :
    operator X v = WithLp.toLp 2 (X *ᵥ ⇑v) := rfl

theorem operator_square (X : Matrix κ κ ℂ) : operator X = Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ) X := rfl

omit [DecidableEq σ] in
/-- The Gram quadratic form is exactly the squared Euclidean output norm. -/
theorem gram_quadratic (X : Matrix σ κ ℂ) (v : EuclideanSpace ℂ κ) :
    (star ⇑v ⬝ᵥ ((Xᴴ * X) *ᵥ ⇑v)).re = ‖operator X v‖ ^ 2 := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_conjTranspose, star_star]
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) (operator X v)
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, operator_apply,
    WithLp.ofLp_toLp, dotProduct_comm] using h

/-- Native spectral bound for every eigenvalue of `I + X†X` on the actual
operator-norm half-ball. -/
theorem metric_eigenvalue_le (X : Matrix σ κ ℂ) (hX : ‖operator X‖ ≤ 1 / 2) (i : κ) :
    (GraphFamily.metric_posDef X).isHermitian.eigenvalues i ≤ 5 / 4 := by
  let hA := (GraphFamily.metric_posDef X).isHermitian
  let v := hA.eigenvectorBasis i
  have hv : ‖v‖ = 1 := hA.eigenvectorBasis.orthonormal.norm_eq_one i
  have hn : ‖operator X v‖ ≤ 1 / 2 := by
    have h := (operator X).le_opNorm v
    rw [hv, mul_one] at h
    exact h.trans hX
  have hself : (star ⇑v ⬝ᵥ ⇑v).re = 1 := by
    have h := inner_self_eq_norm_sq (𝕜 := ℂ) v
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, hv,
      one_pow] using h
  rw [hA.eigenvalues_eq]
  change (star ⇑v ⬝ᵥ ((1 + Xᴴ * X) *ᵥ ⇑v)).re ≤ _
  rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, Complex.add_re,
    hself, gram_quadratic]
  nlinarith [norm_nonneg (operator X v)]

theorem metric_det_pos (X : Matrix σ κ ℂ) : 0 < (GraphFamily.metric X).det.re := by
  rw [(GraphFamily.metric_posDef X).isHermitian.det_eq_prod_eigenvalues,
    RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_prod, Complex.ofReal_re]
  exact Finset.prod_pos fun i _ => (GraphFamily.metric_posDef X).eigenvalues_pos i

/-- The determinant bound in Corollary 2.5 is proved from actual matrix
eigenvalues, not supplied as an external field. -/
theorem metric_det_le (X : Matrix σ κ ℂ) (hX : ‖operator X‖ ≤ 1 / 2) :
    (GraphFamily.metric X).det.re ≤ (5 / 4 : ℝ) ^ Fintype.card κ := by
  rw [(GraphFamily.metric_posDef X).isHermitian.det_eq_prod_eigenvalues,
    RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_prod, Complex.ofReal_re]
  calc
    _ ≤ ∏ _i : κ, (5 / 4 : ℝ) := Finset.prod_le_prod
      (fun i _ => (GraphFamily.metric_posDef X).eigenvalues_pos i |>.le)
      (fun i _ => metric_eigenvalue_le X hX i)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ]

/-- The actual local operator-norm chart. -/
def localChart (r s : ℕ) : Set (TailMatrix r s) := {X | ‖operator X‖ ≤ 1 / 2}

/-- The full inverse density factor bounding local Lebesgue volume. -/
def chartFactor (r s : ℕ) : ℝ :=
  VolumeRates.graphNormalizer s r * (5 / 4 : ℝ) ^ ((r + s) * r)

/-- Exact invariant graph-coordinate density, with the positive real
determinant of the actual graph Gram matrix. -/
def chartWeight (r s : ℕ) (X : TailMatrix r s) : ℝ≥0∞ :=
  (ENNReal.ofReal (VolumeRates.graphNormalizer s r *
    (GraphFamily.metric X).det.re ^ (r + s)))⁻¹

/-- The saturated Haar-frame event corresponding to an actual graph
projector image. All choices of right-unitary frame basis are included. -/
def graphImage (r s : ℕ) (S : Set (TailMatrix r s)) : Set (FrameSpace r s) :=
  {U | ∃ X ∈ S, U.projector.matrix = GraphFamily.projectorMatrix X}

/-- Exact standard Grassmann graph-chart density input, DKM2018
arXiv:1808.06783v1, equations (35), (38), (39), PDF p. 8, after probability
normalization. The only field quantifies arbitrary measurable matrix sets
and their actual Haar projector images; it contains no loss or rate. -/
structure GraphChartInput : Prop where
  image_density : ∀ (r s : ℕ), 0 < r → r ≤ s →
    ∀ (μ : Measure (FrameSpace r s)), IsHaarFrameDistribution μ →
    ∀ S : Set (TailMatrix r s), MeasurableSet S →
      μ (graphImage r s S) = ∫⁻ X in S, chartWeight r s X ∂matrixLebesgue r s

theorem chartFactor_pos (r s : ℕ) : 0 < chartFactor r s :=
  mul_pos (graphNormalizer_pos s r) (by positivity)

/-- The local density lower bound follows from the native determinant
estimate, with the exact exponent `d*r = (r+s)*r`. -/
theorem chartWeight_lower (r s : ℕ) (X : TailMatrix r s) (hX : X ∈ localChart r s) :
    (ENNReal.ofReal (chartFactor r s))⁻¹ ≤ chartWeight r s X := by
  apply ENNReal.inv_le_inv.2
  apply ENNReal.ofReal_le_ofReal
  unfold chartFactor
  have hdet := metric_det_le X hX
  simp only [Fintype.card_fin] at hdet
  have hpow := pow_le_pow_left₀ (metric_det_pos X).le hdet (r + s)
  have heq : ((5 / 4 : ℝ) ^ r) ^ (r + s) = (5 / 4 : ℝ) ^ ((r + s) * r) := by
    rw [← pow_mul, Nat.mul_comm]
  rw [heq] at hpow
  exact mul_le_mul_of_nonneg_left hpow (graphNormalizer_pos s r).le

/-- Generic measurable-set transfer from Haar probability to ordinary
Lebesgue outer volume in the local half-chart. -/
theorem chart_volume_transfer (G : GraphChartInput) (r s : ℕ)
    (hr : 0 < r) (hrs : r ≤ s) (μ : Measure (FrameSpace r s))
    (hμ : IsHaarFrameDistribution μ) (S : Set (TailMatrix r s))
    (hS : MeasurableSet S) (hlocal : S ⊆ localChart r s) :
    matrixLebesgue r s S ≤ ENNReal.ofReal (chartFactor r s) * μ (graphImage r s S) := by
  have hlow : (ENNReal.ofReal (chartFactor r s))⁻¹ * matrixLebesgue r s S ≤
      ∫⁻ X in S, chartWeight r s X ∂matrixLebesgue r s := by
    calc
      _ = ∫⁻ _X in S, (ENNReal.ofReal (chartFactor r s))⁻¹ ∂matrixLebesgue r s := by
        rw [setLIntegral_const]
      _ ≤ _ := setLIntegral_mono' hS fun X hX => chartWeight_lower r s X (hlocal hX)
  rw [← G.image_density r s hr hrs μ hμ S hS] at hlow
  exact (ENNReal.inv_mul_le_iff
    (ENNReal.ofReal_ne_zero_iff.2 (chartFactor_pos r s)) ENNReal.ofReal_ne_top).1 hlow

/-- The half-chart is closed in the ordinary matrix-entry topology. -/
theorem isClosed_localChart (r s : ℕ) : IsClosed (localChart r s) := by
  have heq : localChart r s = ⋂ v : EuclideanSpace ℂ (Fin r),
      {X | ‖operator X v‖ ≤ (1 / 2 : ℝ) * ‖v‖} := by
    ext X
    simp only [localChart, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h v
      exact ((operator X).le_opNorm v).trans (mul_le_mul_of_nonneg_right h (norm_nonneg v))
    · intro h
      exact (operator X).opNorm_le_bound (by norm_num) h
  rw [heq]
  apply isClosed_iInter
  intro v
  apply isClosed_le _ continuous_const
  have h : Continuous (fun X : TailMatrix r s => X *ᵥ ⇑v) :=
    continuous_id.matrix_mulVec continuous_const
  exact ((PiLp.continuous_toLp 2 _).comp h).norm

/-- Kernel inclusion is a closed condition on the actual graph state. -/
theorem isClosed_graph_support [Nonempty κ] (τ : Density (κ ⊕ σ)) :
    IsClosed {X : Matrix σ κ ℂ | SupportContained (GraphFamily.density X) τ} := by
  have heq : {X : Matrix σ κ ℂ | SupportContained (GraphFamily.density X) τ} =
      ⋂ v : (κ ⊕ σ) → ℂ, ⋂ _h : τ.matrix *ᵥ v = 0,
        {X | (GraphFamily.density X).matrix *ᵥ v = 0} := by
    ext X
    simp [SupportContained]
  rw [heq]
  exact isClosed_iInter fun v => isClosed_iInter fun _ =>
    isClosed_eq (GraphFamily.continuous_density_matrix.matrix_mulVec continuous_const)
      continuous_const

theorem continuous_graph_supportDifference [Nonempty κ] (τ : Density (κ ⊕ σ)) :
    Continuous (fun X : Matrix σ κ ℂ => supportDifference (GraphFamily.density X) τ) := by
  unfold supportDifference eigenDifference
  exact ((continuous_const.matrix_mul
    (GraphFamily.continuous_density_matrix.sub continuous_const)).matrix_mul
      continuous_const).matrix_submatrix _ _

theorem continuous_graph_bures [Nonempty κ] (τ : Density (κ ⊕ σ)) :
    Continuous (fun X : Matrix σ κ ℂ =>
      SpectralLoss.bures (supportSpectrum τ) (supportDifference (GraphFamily.density X) τ)) := by
  unfold SpectralLoss.bures
  apply continuous_finset_sum
  intro i _
  apply continuous_finset_sum
  intro j _
  exact (continuous_const.mul (Complex.continuous_normSq.comp
    ((continuous_graph_supportDifference τ).matrix_elem i j))).div_const _

theorem continuous_graph_right [Nonempty κ] (τ : Density (κ ⊕ σ)) :
    Continuous (fun X : Matrix σ κ ℂ =>
      SpectralLoss.rightInverse (supportSpectrum τ) (supportDifference (GraphFamily.density X) τ)) := by
  unfold SpectralLoss.rightInverse
  apply continuous_finset_sum
  intro i _
  apply continuous_finset_sum
  intro j _
  exact (Complex.continuous_normSq.comp
    ((continuous_graph_supportDifference τ).matrix_elem i j)).div_const _

/-- Actual singular-output chi-squared losses remain measurable on graph
coordinates: the finite branch is continuous and kernel inclusion is closed. -/
theorem measurable_graph_chiB [Nonempty κ] (τ : Density (κ ⊕ σ)) :
    Measurable (fun X : Matrix σ κ ℂ => chiB (GraphFamily.density X) τ) := by
  classical
  exact Measurable.ite (isClosed_graph_support τ).measurableSet
    (ENNReal.measurable_ofReal.comp (continuous_graph_bures τ).measurable) measurable_const

theorem measurable_graph_chiR [Nonempty κ] (τ : Density (κ ⊕ σ)) :
    Measurable (fun X : Matrix σ κ ℂ => chiR (GraphFamily.density X) τ) := by
  classical
  exact Measurable.ite (isClosed_graph_support τ).measurableSet
    (ENNReal.measurable_ofReal.comp (continuous_graph_right τ).measurable) measurable_const

/-- The actual local successful parameter set, for an arbitrary loss. -/
def localSuccess (r s : ℕ) [NeZero r]
    (χ : Density (Fin r ⊕ Fin s) → Density (Fin r ⊕ Fin s) → ℝ≥0∞)
    (τ : Density (Fin r ⊕ Fin s)) (ε : ℝ) : Set (TailMatrix r s) :=
  localChart r s ∩ {X | χ (GraphFamily.density X) τ ≤ ENNReal.ofReal ε}

private theorem density_ext {ι : Type*} [Fintype ι] {ρ η : Density ι}
    (h : ρ.matrix = η.matrix) : ρ = η := by
  cases ρ
  cases η
  cases h
  rfl

theorem density_eq_of_projector_eq (r s : ℕ) [NeZero r]
    (U : FrameSpace r s) (X : TailMatrix r s)
    (h : U.projector.matrix = GraphFamily.projectorMatrix X) :
    U.density = GraphFamily.density X := by
  apply density_ext
  rw [Frame.density_matrix, GraphFamily.density_matrix, ← Frame.projector_matrix, h]

theorem graphImage_localSuccess_subset (r s : ℕ) [NeZero r]
    (χ : Density (Fin r ⊕ Fin s) → Density (Fin r ⊕ Fin s) → ℝ≥0∞)
    (τ : Density (Fin r ⊕ Fin s)) (ε : ℝ) :
    graphImage r s (localSuccess r s χ τ ε) ⊆
      {U | χ U.density τ ≤ ENNReal.ofReal ε} := by
  rintro U ⟨X, hX, h⟩
  change χ U.density τ ≤ ENNReal.ofReal ε
  rw [density_eq_of_projector_eq r s U X h]
  exact hX.2

theorem measurableSet_localSuccess_bures (r s : ℕ) [NeZero r]
    (τ : Density (Fin r ⊕ Fin s)) (ε : ℝ) :
    MeasurableSet (localSuccess r s chiB τ ε) :=
  (isClosed_localChart r s).measurableSet.inter
    (measurableSet_le (measurable_graph_chiB τ) measurable_const)

theorem measurableSet_localSuccess_right (r s : ℕ) [NeZero r]
    (τ : Density (Fin r ⊕ Fin s)) (ε : ℝ) :
    MeasurableSet (localSuccess r s chiR τ ε) :=
  (isClosed_localChart r s).measurableSet.inter
    (measurableSet_le (measurable_graph_chiR τ) measurable_const)

/-- Generic transfer of an actual Haar loss-probability bound. The loss
set is defined on the genuine normalized graph projector. -/
theorem localSuccess_volume (G : GraphChartInput) (r s : ℕ) [NeZero r]
    (hr : 0 < r) (hrs : r ≤ s) (μ : Measure (FrameSpace r s))
    (hμ : IsHaarFrameDistribution μ)
    (χ : Density (Fin r ⊕ Fin s) → Density (Fin r ⊕ Fin s) → ℝ≥0∞)
    (τ : Density (Fin r ⊕ Fin s)) (ε p : ℝ)
    (hS : MeasurableSet (localSuccess r s χ τ ε))
    (hp : μ {U | χ U.density τ ≤ ENNReal.ofReal ε} ≤ ENNReal.ofReal p) :
    matrixLebesgue r s (localSuccess r s χ τ ε) ≤
      ENNReal.ofReal (chartFactor r s * p) := by
  calc
    _ ≤ ENNReal.ofReal (chartFactor r s) *
        μ (graphImage r s (localSuccess r s χ τ ε)) :=
      chart_volume_transfer G r s hr hrs μ hμ _ hS (fun _ h => h.1)
    _ ≤ ENNReal.ofReal (chartFactor r s) * ENNReal.ofReal p :=
      mul_le_mul_left' ((measure_mono (graphImage_localSuccess_subset r s χ τ ε)).trans hp) _
    _ = _ := (ENNReal.ofReal_mul (chartFactor_pos r s).le).symm

/-- A convenient universal base for the graph-coordinate volume factor. -/
def chartBase (s : ℕ) : ℝ := 25 * Real.pi * Real.exp 1 / (16 * (s : ℝ))

theorem chartBase_pos (s : ℕ) (hs : 0 < s) : 0 < chartBase s := by
  unfold chartBase
  positivity

theorem chartFactor_upper (r s : ℕ) (hr : 0 < r) (hrs : r ≤ s) :
    chartFactor r s ≤ chartBase s ^ (r * s) := by
  have hs : 0 < s := hr.trans_le hrs
  have hn : (r + s) * r ≤ 2 * (r * s) := by nlinarith
  have hp : (5 / 4 : ℝ) ^ ((r + s) * r) ≤ ((5 / 4 : ℝ) ^ 2) ^ (r * s) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) hn
  calc
    _ ≤ (Real.pi * Real.exp 1 / (s : ℝ)) ^ (r * s) *
        ((5 / 4 : ℝ) ^ 2) ^ (r * s) :=
      mul_le_mul (VolumeNormalizerUpper.graphNormalizer_upper s r hs) hp
        (by positivity) (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; unfold chartBase; ring

/-- Uniform conversion of an `rs`-power Haar probability rate to a
local graph volume rate. -/
theorem localSuccess_volume_power (G : GraphChartInput) (r s : ℕ) [NeZero r]
    (hr : 0 < r) (hrs : r ≤ s) (μ : Measure (FrameSpace r s))
    (hμ : IsHaarFrameDistribution μ)
    (χ : Density (Fin r ⊕ Fin s) → Density (Fin r ⊕ Fin s) → ℝ≥0∞)
    (τ : Density (Fin r ⊕ Fin s)) (ε p : ℝ) (hp0 : 0 ≤ p)
    (hS : MeasurableSet (localSuccess r s χ τ ε))
    (hp : μ {U | χ U.density τ ≤ ENNReal.ofReal ε} ≤ ENNReal.ofReal (p ^ (r * s))) :
    matrixLebesgue r s (localSuccess r s χ τ ε) ≤
      ENNReal.ofReal ((chartBase s * p) ^ (r * s)) := by
  refine (localSuccess_volume G r s hr hrs μ hμ χ τ ε (p ^ (r * s)) hS hp).trans ?_
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ chartBase s ^ (r * s) * p ^ (r * s) :=
      mul_le_mul_of_nonneg_right (chartFactor_upper r s hr hrs) (pow_nonneg hp0 _)
    _ = _ := (mul_pow _ _ _).symm

/-- Real `q`th-root conversion, with finite volume proved by the power bound. -/
theorem volume_root_le (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (S : Set (TailMatrix r s)) (p : ℝ) (hp : 0 ≤ p)
    (hvol : matrixLebesgue r s S ≤ ENNReal.ofReal (p ^ (r * s))) :
    (matrixLebesgue r s S).toReal ^ (1 / ((r * s : ℕ) : ℝ)) ≤ p := by
  have hq : r * s ≠ 0 := Nat.ne_of_gt (Nat.mul_pos hr hs)
  have hreal : (matrixLebesgue r s S).toReal ≤ p ^ (r * s) := by
    simpa only [ENNReal.toReal_ofReal (pow_nonneg hp _)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
  have h := Real.rpow_le_rpow ENNReal.toReal_nonneg hreal
    (show 0 ≤ (((r * s : ℕ) : ℝ)⁻¹) by positivity)
  simpa only [one_div, Real.pow_rpow_inv_natCast hp hq] using h

/-- Corollary 2.5 Bures volume bound in the actual local graph family,
with an explicit universal constant. -/
theorem corollary_2_5_bures (G : GraphChartInput) (r s : ℕ) [NeZero r]
    (hr : 0 < r) (hrs : r ≤ s) (T : TruncatedHaarInput)
    (N : ProperSubspaceNullInput (Fin r ⊕ Fin s) (Fin r))
    (F : TailMass.BuresMetricInput (Fin r ⊕ Fin s))
    (C : TailMassBridges.RawCompressionInput (Fin r ⊕ Fin s) (Fintype.card (Fin r)))
    (L : TailConvexity.LyapunovPositivityInput (Fin s))
    (BM : TailVolume.BrunnMinkowskiInput (Fin s) (Fin r))
    (UL : TailVolume.UnitaryLebesgueInput (Fin s) (Fin r))
    (BV : ScalarTailBall.EuclideanBallVolumeInput (Fin s) (Fin r))
    (μ : Measure (FrameSpace r s)) (hμ : IsHaarFrameDistribution μ)
    (τ : Density (Fin r ⊕ Fin s)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    matrixLebesgue r s (localSuccess r s chiB τ ε) ≤
      ENNReal.ofReal (((75 / 8 : ℝ) * Real.pi * Real.exp 1 ^ 2 * ε / (s : ℝ) *
        Real.sqrt ((r : ℝ) / (s : ℝ))) ^ (r * s)) := by
  have h := localSuccess_volume_power G r s hr hrs μ hμ chiB τ ε
    (6 * Real.exp 1 * ε * Real.sqrt ((r : ℝ) / (s : ℝ))) (by positivity)
    (measurableSet_localSuccess_bures r s τ ε)
    (HaarLossBalls.theorem_2_4_bures r s hr hrs T N F C L BM UL BV μ hμ τ hε hε1)
  convert h using 1
  unfold chartBase
  congr 2
  ring

theorem corollary_2_5_bures_root (G : GraphChartInput) (r s : ℕ) [NeZero r]
    (hr : 0 < r) (hrs : r ≤ s) (T : TruncatedHaarInput)
    (N : ProperSubspaceNullInput (Fin r ⊕ Fin s) (Fin r))
    (F : TailMass.BuresMetricInput (Fin r ⊕ Fin s))
    (C : TailMassBridges.RawCompressionInput (Fin r ⊕ Fin s) (Fintype.card (Fin r)))
    (L : TailConvexity.LyapunovPositivityInput (Fin s))
    (BM : TailVolume.BrunnMinkowskiInput (Fin s) (Fin r))
    (UL : TailVolume.UnitaryLebesgueInput (Fin s) (Fin r))
    (BV : ScalarTailBall.EuclideanBallVolumeInput (Fin s) (Fin r))
    (μ : Measure (FrameSpace r s)) (hμ : IsHaarFrameDistribution μ)
    (τ : Density (Fin r ⊕ Fin s)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    (matrixLebesgue r s (localSuccess r s chiB τ ε)).toReal ^
        (1 / ((r * s : ℕ) : ℝ)) ≤
      (75 / 8 : ℝ) * Real.pi * Real.exp 1 ^ 2 * ε / (s : ℝ) *
        Real.sqrt ((r : ℝ) / (s : ℝ)) :=
  volume_root_le r s hr (hr.trans_le hrs) _ _ (by positivity)
    (corollary_2_5_bures G r s hr hrs T N F C L BM UL BV μ hμ τ hε hε1)

/-- Corollary 2.5 right-inverse volume bound, for every density output,
including singular outputs. -/
theorem corollary_2_5_right (G : GraphChartInput) (r s : ℕ) [NeZero r]
    (hr : 0 < r) (hrs : r ≤ s) (T : TruncatedHaarInput)
    (N : ProperSubspaceNullInput (Fin r ⊕ Fin s) (Fin r))
    (F : TailMass.BuresMetricInput (Fin r ⊕ Fin s))
    (C : TailMassBridges.RawCompressionInput (Fin r ⊕ Fin s) (Fintype.card (Fin r)))
    (J : RightTailVolume.PositiveRowScalingInput (Fin s) (Fin r))
    (BV : ScalarTailBall.EuclideanBallVolumeInput (Fin s) (Fin r))
    (μ : Measure (FrameSpace r s)) (hμ : IsHaarFrameDistribution μ)
    (τ : Density (Fin r ⊕ Fin s)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    matrixLebesgue r s (localSuccess r s chiR τ ε) ≤
      ENNReal.ofReal (((225 / 8 : ℝ) * Real.pi * Real.exp 1 ^ 2 * (r : ℝ) * ε ^ 2 /
        (s : ℝ) ^ 2) ^ (r * s)) := by
  have h := localSuccess_volume_power G r s hr hrs μ hμ chiR τ ε
    (18 * Real.exp 1 * (r : ℝ) * ε ^ 2 / (s : ℝ)) (by positivity)
    (measurableSet_localSuccess_right r s τ ε)
    (HaarLossBalls.theorem_2_4_right r s hr hrs T N F C J BV μ hμ τ hε hε1)
  convert h using 1
  unfold chartBase
  congr 2
  ring

theorem corollary_2_5_right_root (G : GraphChartInput) (r s : ℕ) [NeZero r]
    (hr : 0 < r) (hrs : r ≤ s) (T : TruncatedHaarInput)
    (N : ProperSubspaceNullInput (Fin r ⊕ Fin s) (Fin r))
    (F : TailMass.BuresMetricInput (Fin r ⊕ Fin s))
    (C : TailMassBridges.RawCompressionInput (Fin r ⊕ Fin s) (Fintype.card (Fin r)))
    (J : RightTailVolume.PositiveRowScalingInput (Fin s) (Fin r))
    (BV : ScalarTailBall.EuclideanBallVolumeInput (Fin s) (Fin r))
    (μ : Measure (FrameSpace r s)) (hμ : IsHaarFrameDistribution μ)
    (τ : Density (Fin r ⊕ Fin s)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    (matrixLebesgue r s (localSuccess r s chiR τ ε)).toReal ^
        (1 / ((r * s : ℕ) : ℝ)) ≤
      (225 / 8 : ℝ) * Real.pi * Real.exp 1 ^ 2 * (r : ℝ) * ε ^ 2 / (s : ℝ) ^ 2 :=
  volume_root_le r s hr (hr.trans_le hrs) _ _ (by positivity)
    (corollary_2_5_right G r s hr hrs T N F C J BV μ hμ τ hε hε1)

end Paper26.ChartVolume
