import GeometricMedianCoresets.L1Feature
import GeometricMedianCoresets.GaussianMoment
import GeometricMedianCoresets.NormedMedian
import GeometricMedianCoresets.UniformComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The actual Gaussian L2 realization (Lemma 2.1) and Euclidean Theorem 1.2(i). -/
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory
open scoped BigOperators RealInnerProductSpace
namespace GeometricMedianCoresets.Euclidean
open GaussianProjection

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev FeatureSpace (d : ℕ) := Lp ℝ 2 ((standard d).prod (volume : Measure ℝ))

def rawFeature {d : ℕ} (x : Space d) : FeatureSpace d :=
  L1Feature.feature (project x) (measurable_project x) (integrable_project x)

lemma project_sub {d : ℕ} (x y : Space d) (g : Fin d → ℝ) :
    project (x - y) g = project x g - project y g := by
  simp [project, mul_sub, Finset.sum_sub_distrib]

lemma rawFeature_dist_sq {d : ℕ} (x y : Space d) :
    ‖rawFeature x - rawFeature y‖ ^ 2 = ‖x - y‖ * firstMoment := by
  rw [rawFeature, rawFeature, L1Feature.norm_sub_sq]
  simp_rw [← project_sub]
  exact integral_abs_project (x - y)

/-- `(π/2)^(1/4)`, written with square roots for the norm calculations. -/
def scale : ℝ := Real.sqrt (Real.sqrt (Real.pi / 2))

lemma scale_eq_paper : scale = (Real.pi / 2) ^ (1/4:ℝ) := by
  unfold scale
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (by positivity : 0 ≤ Real.pi / 2)]
  congr 1
  norm_num

lemma scale_normalize : scale ^ 2 * firstMoment = 1 := by
  rw [scale, Real.sq_sqrt (Real.sqrt_nonneg _), firstMoment_eq,
    ← Real.sqrt_mul (by positivity : 0 ≤ Real.pi / 2)]
  have heq : Real.pi / 2 * (2 / Real.pi) = 1 := by field_simp
  rw [heq]
  norm_num

/-- The Gaussian subgraph feature anchored at the population reference point. -/
def feature {d : ℕ} (μ x : Space d) : FeatureSpace d :=
  scale • (rawFeature x - rawFeature μ)

/-- Lemma 2.1: the feature vanishes at its anchor. -/
theorem feature_anchor {d : ℕ} (μ : Space d) : feature μ μ = 0 := by
  simp [feature]

/-- Lemma 2.1: Euclidean distance is the squared distance in the actual product-measure L2. -/
theorem feature_dist_sq {d : ℕ} (μ x y : Space d) :
    ‖feature μ x - feature μ y‖ ^ 2 = ‖x - y‖ := by
  have heq : feature μ x - feature μ y = scale • (rawFeature x - rawFeature y) := by
    unfold feature
    rw [← smul_sub]
    congr 1
    abel
  rw [heq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, rawFeature_dist_sq]
  calc scale ^ 2 * (‖x - y‖ * firstMoment) = (scale ^ 2 * firstMoment) * ‖x - y‖ := by ring
    _ = ‖x - y‖ := by rw [scale_normalize, one_mul]

/-- The actual representatives agree almost everywhere with the paper's indicator formula. -/
theorem feature_ae_formula {d : ℕ} (μ x : Space d) :
    (feature μ x : (Fin d → ℝ) × ℝ → ℝ) =ᵐ[(standard d).prod volume]
      fun p => (Real.pi / 2) ^ (1/4:ℝ) *
        ((if p.2 ≤ project x p.1 then 1 else 0) -
          (if p.2 ≤ project μ p.1 then 1 else 0)) := by
  have hx := (L1Feature.step_memLp (ν := standard d) (measurable_project x)
    (integrable_project x)).coeFn_toLp
  have hμ := (L1Feature.step_memLp (ν := standard d) (measurable_project μ)
    (integrable_project μ)).coeFn_toLp
  filter_upwards [Lp.coeFn_smul scale (rawFeature x - rawFeature μ),
    Lp.coeFn_sub (rawFeature x) (rawFeature μ), hx, hμ] with p hs hsub hx hμ
  change rawFeature x p = RealFeature.step (project x p.1) p.2 at hx
  change rawFeature μ p = RealFeature.step (project μ p.1) p.2 at hμ
  change (scale • (rawFeature x - rawFeature μ)) p = _
  rw [hs]
  change scale * ((rawFeature x - rawFeature μ) p) = _
  rw [hsub]
  change scale * (rawFeature x p - rawFeature μ p) = _
  rw [hx, hμ, RealFeature.step_halfline, RealFeature.step_halfline, scale_eq_paper]
  ring

/-- Anchored norm identity at each input point, hence the exact OPT second moment. -/
theorem feature_norm_sq {d : ℕ} (μ p : Space d) : ‖feature μ p‖ ^ 2 = ‖p - μ‖ := by
  simpa [feature_anchor] using feature_dist_sq μ p μ

def squaredMetric (d : ℕ) : SquaredMetric (Space d) where
  H := FeatureSpace d
  d x y := ‖x - y‖
  Φ := feature 0
  dist_sq := feature_dist_sq 0
  triangle x y z := by
    simpa only [sub_add_sub_cancel] using norm_add_le (x - z) (z - y)

/-- Theorem 1.2(i) for actual Euclidean input and every candidate point. -/
theorem thm_1_2_i {d n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (P : Dataset (Space d) n) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4)
    (hmsize : ⌈20 / (ε * ε)⌉₊ ≤ m) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => IsStableCoreset (normDist (Space d)) P (indexedSample P I) ε (17 * ε))).card
      / (n.choose m : ℝ) ≥ 4 / 5 := by
  obtain ⟨μ, hμ⟩ := exists_normed_geometricMedian hn P
  exact uniform_stable_4_5_ceil (squaredMetric d) hn hm hmn P μ hμ hε hε' hmsize

/-- Theorem 1.2(i) with the practical `min(n,ceil(20/ε²))` sample rule. -/
theorem thm_1_2_i_min {d n : ℕ} (hn : 0 < n) (P : Dataset (Space d) n)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4) :
    let m := min n ⌈20 / (ε * ε)⌉₊
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => IsStableCoreset (normDist (Space d)) P (indexedSample P I) ε (17 * ε))).card
      / (n.choose m : ℝ) ≥ 4 / 5 := by
  obtain ⟨μ, hμ⟩ := exists_normed_geometricMedian hn P
  exact uniform_stable_min (squaredMetric d) hn P μ hμ hε hε'

/-- Proposition 2.4 on actual Euclidean data, with its all-pairs event inside probability. -/
theorem prop24 {d n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n)
    (P : Dataset (Space d) n) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => ∀ x y, |(normDist (Space d)).delta P (indexedSample P I) x y| ≤
        Real.sqrt (20 / m) * ((normDist (Space d)).cost P x + (normDist (Space d)).cost P y))).card
      / (n.choose m : ℝ) ≥ 9 / 10 := by
  obtain ⟨μ, hμ⟩ := exists_normed_geometricMedian hn P
  exact uniform_comparison_9_10 (squaredMetric d) hn hm hmn P μ hμ

end GeometricMedianCoresets.Euclidean
