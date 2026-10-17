import Paper35.GaussianWinner
import Paper35.CurveCalculus
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-! Actual Gaussian layers with arbitrary dependence between units. The exact
active moment is imported from the proved winner formula, never postulated. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ENNReal NNReal
namespace Paper35.GaussianLayer
open Paper35.Deep Paper35.GaussianWinner

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure Layer (d q : ℕ) where
  rankMinusOne : Fin q → ℕ
  unit : Fin q → GaussianUnit d
  law : Measure ((r : Fin q) → GaussianUnit.Sample d (rankMinusOne r + 1))
  probability : IsProbabilityMeasure law
  marginal : ∀ r, law.map (fun θ => θ r) = (unit r).sampleLaw (rankMinusOne r+1)

namespace Layer
variable {d q : ℕ} (g : Layer d q)

abbrev Parameter := (r : Fin q) → GaussianUnit.Sample d (g.rankMinusOne r+1)

def layerMap (θ : g.Parameter) (z : Space d) : Space q :=
  WithLp.toLp 2 (fun r => (g.unit r).maxValue (g.rankMinusOne r) (fun i => z i) (θ r))

/-- Actual selected projected-weight vector at the point z and direction v. -/
def activeProjection (z v : Fin d → ℝ) (θ : g.Parameter) : Space q :=
  WithLp.toLp 2 (fun r => v ⬝ᵥ (g.unit r).activeWeight (g.rankMinusOne r) z (θ r))

/-- The sum of the source Q_r(z) matrices. -/
def totalQ (z : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ r, activeSecondMomentMatrix (g.unit r).covariance z ((g.unit r).scoreVariance z)
    (gaussianMaxSecondMoment (g.rankMinusOne r+1))

lemma unitProjection_memLp (haffine : AffineGaussianLawInput)
    (hregression : GaussianRegressionInput) (hmarking : IndependentMarkingInput)
    (r : Fin q) (z v : Fin d → ℝ) :
    MemLp (fun ω => v ⬝ᵥ (g.unit r).activeWeight (g.rankMinusOne r) z ω) 2
      ((g.unit r).sampleLaw (g.rankMinusOne r+1)) := by
  apply memLp_finset_sum
  intro i hi
  exact ((g.unit r).activeWeight_memLp haffine hregression hmarking _ z i).const_mul (v i)

lemma projectionCoordinate_memLp (haffine : AffineGaussianLawInput)
    (hregression : GaussianRegressionInput) (hmarking : IndependentMarkingInput)
    (r : Fin q) (z v : Fin d → ℝ) :
    MemLp (fun θ : g.Parameter => v ⬝ᵥ (g.unit r).activeWeight (g.rankMinusOne r) z (θ r)) 2 g.law := by
  have hm : MemLp (fun ω => v ⬝ᵥ (g.unit r).activeWeight (g.rankMinusOne r) z ω) 2
      (g.law.map (fun θ => θ r)) := by
    rw [g.marginal r]
    exact g.unitProjection_memLp haffine hregression hmarking r z v
  exact hm.comp_of_map (measurable_pi_apply r).aemeasurable

lemma activeProjection_memLp (haffine : AffineGaussianLawInput)
    (hregression : GaussianRegressionInput) (hmarking : IndependentMarkingInput)
    (z v : Fin d → ℝ) : MemLp (g.activeProjection z v) 2 g.law := by
  apply MemLp.of_eval_piLp
  intro r
  exact g.projectionCoordinate_memLp haffine hregression hmarking r z v

/-- The exact sum of second moments requires only each marginal unit law;
no independence between units appears. -/
theorem activeProjection_secondMoment (haffine : AffineGaussianLawInput)
    (hregression : GaussianRegressionInput) (hmarking : IndependentMarkingInput)
    (z v : Fin d → ℝ) :
    (∫ θ, ‖g.activeProjection z v θ‖^2 ∂g.law) = covarianceForm (g.totalQ z) v v := by
  simp_rw [EuclideanSpace.norm_sq_eq]
  simp only [activeProjection, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
  rw [integral_finset_sum _ (fun r _ =>
    (g.projectionCoordinate_memLp haffine hregression hmarking r z v).integrable_sq)]
  have hr (r : Fin q) :
      (∫ θ : g.Parameter, (v ⬝ᵥ (g.unit r).activeWeight (g.rankMinusOne r) z (θ r))^2 ∂g.law) =
      covarianceForm (activeSecondMomentMatrix (g.unit r).covariance z ((g.unit r).scoreVariance z)
        (gaussianMaxSecondMoment (g.rankMinusOne r+1))) v v := by
    have hfun : AEStronglyMeasurable
        (fun ω => (v ⬝ᵥ (g.unit r).activeWeight (g.rankMinusOne r) z ω)^2)
        (g.law.map (fun θ => θ r)) := by
      rw [g.marginal r]
      exact (g.unitProjection_memLp haffine hregression hmarking r z v).integrable_sq.aestronglyMeasurable
    have H := integral_map (μ := g.law) (φ := fun θ : g.Parameter => θ r)
      (measurable_pi_apply r).aemeasurable hfun
    rw [g.marginal r] at H
    rw [← H]
    exact (g.unit r).activeProjection_secondMoment haffine hregression hmarking _ z v
  simp_rw [hr]
  simp only [totalQ, covarianceForm, Matrix.sum_mulVec, dotProduct_sum]

/-- The Jensen step in (8.20), now with actual selected Gaussian weights. -/
theorem expected_activeProjection_norm_le (haffine : AffineGaussianLawInput)
    (hregression : GaussianRegressionInput) (hmarking : IndependentMarkingInput)
    (z v : Fin d → ℝ) :
    (∫ θ, ‖g.activeProjection z v θ‖ ∂g.law) ≤ Real.sqrt (covarianceForm (g.totalQ z) v v) := by
  letI := g.probability
  have hB := g.activeProjection_memLp haffine hregression hmarking z v
  apply Real.le_sqrt_of_sq_le
  have H := Paper35.Deep.mean_square_le_second_moment g.law
    (fun θ => ‖g.activeProjection z v θ‖) hB.norm
  rwa [g.activeProjection_secondMoment haffine hregression hmarking z v] at H

end Layer

/-- Internal AC finite-max specialization, proved from network-independent
classical statements below. It contains the first moment of
the actual derivative vector. There is no Q or rank-dependent factor in this
input. Hypotheses are exactly a finite interval, an AC deterministic curve and
the current-layer Gaussian model; a random independent input is conditioned on
before this statement is applied. -/
def GaussianCurveCalculusInput : Prop :=
  ∀ (d q : ℕ) (g : Layer d q) (T : ℝ) (hT : 0 < T) (η : ℝ → Space d),
    AbsolutelyContinuousOnInterval η 0 T →
    (∫⁻ θ, eVariationOn (fun t => g.layerMap θ (η t)) (Icc 0 T) ∂g.law) ≤
      ∫⁻ s in Icc 0 T, ENNReal.ofReal
        (∫ θ, ‖g.activeProjection (fun i => η s i) (fun i => (deriv η s) i) θ‖ ∂g.law)

namespace Layer
variable {d q : ℕ} (g : Layer d q)

/-- Equation (8.20), for the actual current-layer parameter law, conditional on
the incoming AC curve. Winner Q and the Jensen/moment step are proved above. -/
theorem source_curve_length_bound (haffine : AffineGaussianLawInput)
    (hregression : GaussianRegressionInput) (hmarking : IndependentMarkingInput)
    (hcalculus : GaussianCurveCalculusInput)
    (T : ℝ) (hT : 0 < T) (η : ℝ → Space d)
    (hη : AbsolutelyContinuousOnInterval η 0 T) :
    (∫⁻ θ, eVariationOn (fun t => g.layerMap θ (η t)) (Icc 0 T) ∂g.law) ≤
      ∫⁻ s in Icc 0 T, ENNReal.ofReal
        (Real.sqrt (covarianceForm (g.totalQ (fun i => η s i))
          (fun i => (deriv η s) i) (fun i => (deriv η s) i))) := by
  apply (hcalculus d q g T hT η hη).trans
  apply lintegral_mono
  intro s
  exact ENNReal.ofReal_le_ofReal
    (g.expected_activeProjection_norm_le haffine hregression hmarking _ _)

end Layer
/-- Euclidean coordinates identify the ordinary real inner product with a
finite coordinate dot product. -/
lemma weight_inner_eq {d : ℕ} (w : Fin d → ℝ) (v : Space d) :
    inner ℝ (WithLp.toLp 2 w) v = w ⬝ᵥ (fun i => v i) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Pi.star_apply, star_trivial,
    PiLp.toLp_apply]
  exact dotProduct_comm _ _

set_option maxHeartbeats 800000 in
/-- The Gaussian-specific calculus interface is a specialization of the
arbitrary scalar-family AC chain rule and actual Tonelli theorem. Gaussian
regression/marking inputs are used only to justify integrability. -/
theorem gaussianCurveCalculus_of_classical
    (haffine : AffineGaussianLawInput) (hregression : GaussianRegressionInput)
    (hmarking : IndependentMarkingInput)
    (hlinear : Paper35.CurveCalculus.LinearACCalculusInput)
    (hmax : Paper35.CurveCalculus.FiniteMaxACCalculusInput) :
    GaussianCurveCalculusInput := by
  intro d q g T hT η hη
  letI := g.probability
  let J (s : ℝ) (θ : g.Parameter) (r : Fin q) :=
    (g.unit r).winner (g.rankMinusOne r) (fun i => η s i) (θ r)
  have hscalar := (hlinear d T η hη).2
  have hd := (hlinear d T η hη).1
  have hvar (θ : g.Parameter) :
      eVariationOn (fun t => g.layerMap θ (η t)) (Icc 0 T) =
        ∫⁻ s in Icc 0 T, ENNReal.ofReal
          ‖g.activeProjection (fun i => η s i) (fun i => (deriv η s) i) θ‖ := by
    have H := hmax q (fun r => g.rankMinusOne r+1) (fun r => Nat.succ_pos _) T
      (fun r j s => (θ r j).1 ⬝ᵥ (fun i => η s i)+(θ r j).2)
      (fun r j s => (fun i => (deriv η s) i) ⬝ᵥ (θ r j).1)
      (fun s r => J s θ r) (by
        intro r j
        simpa only [innerSL_apply, weight_inner_eq] using
          hscalar (innerSL ℝ (WithLp.toLp 2 (θ r j).1)) (θ r j).2) (by
        intro r j
        filter_upwards [hd] with s hs
        have H := ((hasDerivAt_const s (WithLp.toLp 2 (θ r j).1)).inner ℝ hs).add_const (θ r j).2
        simpa only [inner_zero_left, add_zero, weight_inner_eq, dotProduct_comm] using H)
      (fun s r j => (g.unit r).winner_is_max _ _ _ j)
    simpa only [Layer.layerMap, GaussianUnit.maxValue,
      Paper35.CurveCalculus.finiteMax_eq_finiteSup, Layer.activeProjection,
      GaussianUnit.activeWeight, J] using H
  have hF : Measurable (fun p : (Space d × Space d) × g.Parameter =>
      g.activeProjection (fun i => p.1.1 i) (fun i => p.1.2 i) p.2) := by
    apply (PiLp.continuous_toLp 2 _).measurable.comp
    apply measurable_pi_lambda
    intro r
    have hJ : Measurable (fun p : (Space d × Space d) × g.Parameter =>
        (g.unit r).winner (g.rankMinusOne r) (fun i => p.1.1 i) (p.2 r)) := by
      apply (measurable_finiteWinner _).comp
      unfold GaussianUnit.scores dotProduct
      fun_prop
    have hW : Measurable (fun p : (Space d × Space d) × g.Parameter =>
        WithLp.toLp 2 ((p.2 r ((g.unit r).winner (g.rankMinusOne r)
          (fun i => p.1.1 i) (p.2 r))).1)) := by
      exact Paper35.CurveCalculus.measurable_finite_selection d
        (fun j (p : (Space d × Space d) × g.Parameter) => WithLp.toLp 2 (p.2 r j).1)
        (fun j => by fun_prop) _ hJ
    have H := Measurable.inner (𝕜 := ℝ) hW (measurable_fst.snd)
    simpa only [Layer.activeProjection, GaussianUnit.activeWeight, PiLp.toLp_apply,
      weight_inner_eq, dotProduct_comm] using H
  have hηcont : ContinuousOn η (Icc 0 T) := hη.continuousOn.mono Icc_subset_uIcc
  have hηmeas : AEMeasurable η (volume.restrict (Icc 0 T)) :=
    hηcont.aemeasurable measurableSet_Icc
  have hparam : AEMeasurable (fun p : ℝ × g.Parameter => ((η p.1,deriv η p.1),p.2))
      ((volume.restrict (Icc 0 T)).prod g.law) :=
    (hηmeas.comp_fst.prodMk (measurable_deriv η).aemeasurable.comp_fst).prodMk
      measurable_snd.aemeasurable
  have hB := hF.comp_aemeasurable hparam
  dsimp only [Function.comp_def] at hB
  exact (Paper35.CurveCalculus.expected_variation_from_derivative g.law q T
    (fun θ t => g.layerMap θ (η t))
    (fun s θ => g.activeProjection (fun i => η s i) (fun i => (deriv η s) i) θ)
    hB (fun s => (g.activeProjection_memLp haffine hregression hmarking _ _).norm.integrable
      (by norm_num)) hvar).le

end Paper35.GaussianLayer
