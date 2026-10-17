import Paper35.GaussianMarked
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal MatrixOrder
namespace Paper35.GaussianLift

open Source

def rootMap {m : ℕ} (Ω : Matrix (Fin m) (Fin m) ℝ) : Space m →L[ℝ] Space m :=
  (Matrix.toEuclideanLin (CFC.sqrt Ω)).toContinuousLinearMap

def covarianceForm {m : ℕ} (Ω : Matrix (Fin m) (Fin m) ℝ) (q : Space m) : ℝ :=
  inner ℝ q (Matrix.toEuclideanLin Ω q)

lemma rootMap_symmetric {m : ℕ} (Ω : Matrix (Fin m) (Fin m) ℝ) :
    (rootMap Ω).toLinearMap.IsSymmetric := by
  exact Matrix.isHermitian_iff_isSymmetric.1 (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg Ω)).1

lemma rootMap_sq {m : ℕ} (Ω : Matrix (Fin m) (Fin m) ℝ) (hΩ : Ω.PosSemidef)
    (q : Space m) : rootMap Ω (rootMap Ω q) = Matrix.toEuclideanLin Ω q := by
  change Matrix.toEuclideanLin (CFC.sqrt Ω) (Matrix.toEuclideanLin (CFC.sqrt Ω) q) = _
  simp only [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp]
  rw [Matrix.mulVec_mulVec, CFC.sqrt_mul_sqrt_self Ω hΩ.nonneg]

lemma norm_rootMap_sq {m : ℕ} (Ω : Matrix (Fin m) (Fin m) ℝ) (hΩ : Ω.PosSemidef)
    (q : Space m) : ‖rootMap Ω q‖^2 = covarianceForm Ω q := by
  rw [← real_inner_self_eq_norm_sq]
  calc
    _ = inner ℝ q (rootMap Ω (rootMap Ω q)) := rootMap_symmetric Ω q (rootMap Ω q)
    _ = _ := by rw [rootMap_sq Ω hΩ]; rfl

lemma rootMap_ne_zero {m : ℕ} (Ω : Matrix (Fin m) (Fin m) ℝ) (hΩ : Ω.PosSemidef)
    (q : Space m) (hq : 0 < covarianceForm Ω q) : rootMap Ω q ≠ 0 := by
  intro hz
  have H := norm_rootMap_sq Ω hΩ q
  rw [hz, norm_zero, zero_pow (by norm_num)] at H
  linarith

lemma normalize_dist_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) :
    dist (Gaussian.normalize x) (Gaussian.normalize y) ≤ 2 * dist x y / ‖x‖ := by
  have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hy' : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hsplit : Gaussian.normalize x - Gaussian.normalize y =
      ‖x‖⁻¹ • (x-y) + (‖x‖⁻¹-‖y‖⁻¹) • y := by
    simp only [Gaussian.normalize, smul_sub, sub_smul]
    abel
  have hi : |‖x‖⁻¹-‖y‖⁻¹| = dist ‖x‖ ‖y‖ / (‖x‖*‖y‖) := by
    simpa only [Real.dist_eq, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      using dist_inv_inv₀ hx' hy'
  rw [dist_eq_norm, hsplit]
  calc
    _ ≤ ‖‖x‖⁻¹ • (x-y)‖ + ‖(‖x‖⁻¹-‖y‖⁻¹) • y‖ := norm_add_le _ _
    _ = ‖x-y‖/‖x‖ + dist ‖x‖ ‖y‖/‖x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_nonneg (norm_nonneg x), Real.norm_eq_abs, hi]
      field_simp
    _ ≤ ‖x-y‖/‖x‖ + dist x y/‖x‖ := by
      simpa only [dist_eq_norm] using
        add_le_add_left (div_le_div_of_nonneg_right (dist_norm_norm_le x y) (norm_nonneg x)) (‖x-y‖/‖x‖)
    _ = _ := by rw [dist_eq_norm]; ring

lemma normalized_lipschitzOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : ℝ → E} {L : ℝ} {K : ℝ≥0} (hL : 0 ≤ L)
    (hf : LipschitzOnWith K f (Icc 0 L)) (hzero : ∀ s ∈ Icc 0 L, f s ≠ 0) :
    ∃ C : ℝ≥0, LipschitzOnWith C (fun s => Gaussian.normalize (f s)) (Icc 0 L) := by
  obtain ⟨c, hc, hbound⟩ := Gaussian.exists_positive_radius hL hf.continuousOn hzero
  refine ⟨⟨2*(K:ℝ)/c, by positivity⟩, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  have hd := normalize_dist_le (f x) (f y) (hzero x hx) (hzero y hy)
  calc
    _ ≤ 2 * dist (f x) (f y)/‖f x‖ := hd
    _ ≤ 2 * ((K:ℝ)*dist x y)/c := by
      apply div_le_div₀ (by positivity)
      · exact mul_le_mul_of_nonneg_left (hf.dist_le_mul x hx y hy) (by norm_num)
      · exact hc
      · exact hbound x hx
    _ = _ := by simp only [NNReal.coe_mk]; ring

/-- The affine feature q_x=(x,1), with the bias as the last coordinate. -/
def feature {d : ℕ} (x : Space d) : Space (d+1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) 1)

lemma feature_dist {d : ℕ} (x y : Space d) : dist (feature x) (feature y) = dist x y := by
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, Fin.sum_univ_castSucc]
  simp [feature, Fin.snoc_castSucc, Fin.snoc_last]

lemma feature_lipschitz (d : ℕ) : LipschitzWith 1 (feature (d := d)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [feature_dist, NNReal.coe_one, one_mul, le_refl]

/-- The source covariance-normalized feature map, using the actual principal
positive-semidefinite matrix square root. -/
def psi {d : ℕ} (Ω : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) (x : Space d) : Space (d+1) :=
  Gaussian.normalize (rootMap Ω (feature x))

lemma psi_unit {d : ℕ} (Ω : Matrix (Fin (d+1)) (Fin (d+1)) ℝ)
    (hΩ : Ω.PosSemidef) (x : Space d) (hx : 0 < covarianceForm Ω (feature x)) :
    ‖psi Ω x‖ = 1 := Gaussian.normalize_norm _ (rootMap_ne_zero Ω hΩ _ hx)

/-- Nonvanishing only on the probe suffices: normalization is Lipschitz on the
compact lifted range, hence genuinely absolutely continuous on the source interval. -/
theorem psi_probe_absolutelyContinuous {d : ℕ}
    (Ω : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) (hΩ : Ω.PosSemidef)
    (p : Probe d) (hvar : ∀ s ∈ Icc 0 p.length, 0 < covarianceForm Ω (feature (p.curve s))) :
    AbsolutelyContinuousOnInterval (fun s => psi Ω (p.curve s)) 0 p.length := by
  have hq : LipschitzOnWith 1 (fun s => feature (p.curve s)) (Icc 0 p.length) := by
    simpa only [one_mul] using (feature_lipschitz d).comp_lipschitzOnWith p.lipschitz
  have hr := (rootMap Ω).lipschitz.comp_lipschitzOnWith hq
  obtain ⟨C, hC⟩ := normalized_lipschitzOn p.length_pos.le hr
    (fun s hs => rootMap_ne_zero Ω hΩ _ (hvar s hs))
  have hC' : LipschitzOnWith C (fun s => psi Ω (p.curve s)) (uIcc 0 p.length) := by
    simpa only [uIcc_of_le p.length_pos.le, psi, Function.comp_apply] using hC
  exact hC'.absolutelyContinuousOnInterval

/-- A real Gaussian vector law, specified by every linear projection. This
characterization retains arbitrary means and singular PSD covariance matrices. -/
structure Model (m : ℕ) where
  law : Measure (Space m)
  probability : IsProbabilityMeasure law
  mean : Space m
  covariance : Matrix (Fin m) (Fin m) ℝ
  covariance_psd : covariance.PosSemidef
  projections : ∀ v : Space m, law.map (fun θ => inner ℝ θ v) =
    gaussianReal (inner ℝ mean v) (covarianceForm covariance v).toNNReal

/-- Classical finite-dimensional Gaussian linear-image/uniqueness theorem.
Every real Gaussian vector with given mean and PSD covariance is the affine
image of an isotropic Gaussian by the principal covariance square root. The
statement includes singular covariance and dimension zero; it contains no
path, switch count, visibility or rank coefficient. -/
def GaussianRepresentationLaw : Prop :=
  ∀ (m : ℕ) (g : Model m),
    g.law = (GaussianMarked.standardGaussian m).map
      (fun z => g.mean + rootMap g.covariance z)

namespace Model
instance {m : ℕ} (g : Model m) : IsProbabilityMeasure g.law := g.probability

def sampleLaw {m : ℕ} (g : Model m) (K : ℕ) : Measure (Fin K → Space m) :=
  Measure.pi (fun _ => g.law)
instance {m : ℕ} (g : Model m) (K : ℕ) : IsProbabilityMeasure (g.sampleLaw K) := by
  unfold sampleLaw
  infer_instance

/-- The iid affine sample transport is proved from the classical single-vector law. -/
theorem sampleLaw_eq_map (hrep : GaussianRepresentationLaw) {m : ℕ} (g : Model m) (K : ℕ) :
    g.sampleLaw K = (Measure.pi (fun _ : Fin K => GaussianMarked.standardGaussian m)).map
      (fun Z j => g.mean + rootMap g.covariance (Z j)) := by
  have H := Measure.pi_map_pi (μ := fun _ : Fin K => GaussianMarked.standardGaussian m)
    (f := fun _ z => g.mean + rootMap g.covariance z) (fun _ => (by fun_prop))
  simp_rw [← hrep m g] at H
  exact H.symm

end Model

/-- Original affine weight/bias scores in augmented coordinates. -/
def scores {d K : ℕ} (p : Probe d) (θ : Fin K → Space (d+1)) : Fin K → ℝ → ℝ :=
  fun j s => inner ℝ (θ j) (feature (p.curve s))

/-- On a nonvanishing source probe, common mean and positive covariance scale
preserve the actual definition of active switches. -/
theorem covariance_sample_switchSet {d K : ℕ} (g : Model (d+1)) (p : Probe d)
    (hvar : ∀ s ∈ Icc 0 p.length, 0 < covarianceForm g.covariance (feature (p.curve s)))
    (Z : Fin K → Space (d+1)) :
    switchSet (scores p (fun j => g.mean + rootMap g.covariance (Z j))) p.length =
      switchSet (fun j s => inner ℝ (Z j) (psi g.covariance (p.curve s))) p.length := by
  have heq : scores p (fun j => g.mean + rootMap g.covariance (Z j)) =
      fun j s => inner ℝ g.mean (feature (p.curve s)) +
        inner ℝ (Z j) (rootMap g.covariance (feature (p.curve s))) := by
    funext j s
    rw [scores, inner_add_left]
    congr 1
    exact rootMap_symmetric g.covariance _ _
  rw [heq]
  exact Gaussian.covarianceLift_switchSet_on _ _ _ p.length
    (fun s hs => rootMap_ne_zero g.covariance g.covariance_psd _ (hvar s ⟨hs.1.le, hs.2.le⟩))

end Paper35.GaussianLift
