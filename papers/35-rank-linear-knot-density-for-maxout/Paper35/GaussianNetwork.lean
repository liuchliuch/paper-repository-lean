import Paper35.DeepExpectations
import Paper35.GaussianLayer
import Paper35.DeepSwitch
import Paper35.IndependentMarking
import Paper35.GaussianFactors
import Paper35.GaussianUnitAdapter
import Paper35.GaussianUnitDirectional

/-! Actual independent-layer Gaussian Maxout networks. Source parameters are
transported to the Euclidean actual Network by their genuine measurable maps;
there are no one-layer estimate fields in this model. -/
noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators ENNReal NNReal
namespace Paper35.GaussianLayer.Layer
open Paper35.Deep Paper35.GaussianWinner Paper35.CurveCalculus
variable {d q : ℕ} (g : Paper35.GaussianLayer.Layer d q)

def sourceA : ℝ≥0 := ⟨Paper35.GaussianFactors.A (fun r => g.rankMinusOne r+1)
  (fun r => (g.unit r).covariance),Real.sqrt_nonneg _⟩

def sourceD : ℝ≥0 := ⟨Paper35.GaussianFactors.D (fun r => g.rankMinusOne r+1)
  (fun r => (g.unit r).covariance) (fun r => (g.unit r).biasSd),
    Paper35.GaussianFactors.D_nonneg _ _ _ (fun r => (g.unit r).biasSd_pos)⟩

lemma layerMap_lipschitz (θ : g.Parameter) : ∃ C : ℝ≥0, LipschitzWith C (g.layerMap θ) := by
  have H := affineMax_lipschitz d q (fun r => g.rankMinusOne r+1) (fun r => Nat.succ_pos _)
    (fun r j => WithLp.toLp 2 (θ r j).1) (fun r j => (θ r j).2)
  obtain ⟨C,hC⟩ := H
  refine ⟨C,?_⟩
  have heq : g.layerMap θ = (fun x : Space d => WithLp.toLp 2
      (fun r => finiteSup (Nat.succ_pos (g.rankMinusOne r))
        (fun j => inner ℝ (WithLp.toLp 2 (θ r j).1) x+(θ r j).2))) := by
    funext x
    ext r
    change finiteMax (g.rankMinusOne r) _ = finiteSup (Nat.succ_pos (g.rankMinusOne r)) _
    rw [finiteMax_eq_finiteSup]
    congr 1
    funext j
    exact congrArg (fun y => y+(θ r j).2)
      (Paper35.GaussianLayer.weight_inner_eq (θ r j).1 x).symm
  rw [heq]
  exact hC

lemma Q_quadratic_unit_le_sourceA (z : Fin d → ℝ) (v : Space d) (hv : ‖v‖=1) :
    covarianceForm (g.totalQ z) (fun i => v i) (fun i => v i) ≤ (g.sourceA : ℝ)^2 := by
  let C := ∑ r, gaussianLengthCorrection (g.rankMinusOne r+1) • (g.unit r).covariance
  have hr (r : Fin q) :
      covarianceForm (activeSecondMomentMatrix (g.unit r).covariance z ((g.unit r).scoreVariance z)
        (gaussianMaxSecondMoment (g.rankMinusOne r+1))) (fun i => v i) (fun i => v i) ≤
      covarianceForm (gaussianLengthCorrection (g.rankMinusOne r+1) • (g.unit r).covariance)
        (fun i => v i) (fun i => v i) := by
    have H := (gaussian_secondMomentMatrix_domination (g.unit r).covariance_psd z
      (g.unit r).biasSd_pos (g.rankMinusOne r+1)).2 (fun i => v i)
    simp only [Matrix.sub_mulVec,dotProduct_sub] at H
    exact sub_nonneg.mp H
  have Hsum : covarianceForm (g.totalQ z) (fun i => v i) (fun i => v i) ≤
      covarianceForm C (fun i => v i) (fun i => v i) := by
    simp only [totalQ,C,covarianceForm,Matrix.sum_mulVec,dotProduct_sum]
    exact Finset.sum_le_sum (fun r _ => hr r)
  apply Hsum.trans
  have H := Paper35.GaussianFactors.quadratic_unit_le_covarianceMax C v hv
  have hn : 0 ≤ Paper35.GaussianIndependent.covarianceMax C := norm_nonneg _
  change covarianceForm C (fun i => v i) (fun i => v i) ≤ (Real.sqrt (Paper35.GaussianIndependent.covarianceMax C))^2
  rw [Real.sq_sqrt hn]
  exact H

set_option maxHeartbeats 600000 in
/-- The exact Gaussian Q moment and ordinary curve calculus give the actual
one-layer A_G estimate for every rectifiable input curve. -/
theorem rectifiable_length_bound (haffine : AffineGaussianLawInput)
    (hregression : GaussianRegressionInput) (harc : ArclengthFactorizationInput)
    (hlinear : LinearACCalculusInput) (hmax : FiniteMaxACCalculusInput)
    (hd : 0 < d) (η : ℝ → Space d) (L : ℝ)
    (hcont : ContinuousOn η (Icc 0 L)) (hfinite : eVariationOn η (Icc 0 L) ≠ ∞) :
    (∫⁻ θ, eVariationOn (fun t => g.layerMap θ (η t)) (Icc 0 L) ∂g.law) ≤
      (g.sourceA : ℝ≥0∞)*eVariationOn η (Icc 0 L) := by
  obtain ⟨x,u,hx,hmu,hu,hderiv,hrep⟩ :=
    arclengthRepresentation_of_factorization harc d hd η L hcont hfinite
  let T := (eVariationOn η (Icc 0 L)).toReal
  have heq (θ : g.Parameter) : eVariationOn (fun t => g.layerMap θ (η t)) (Icc 0 L) =
      eVariationOn (fun t => g.layerMap θ (x t)) (Icc 0 T) := by
    obtain ⟨C,hC⟩ := g.layerMap_lipschitz θ
    have H := hrep q (g.layerMap θ) C hC
    dsimp only [Function.comp_def] at H
    exact H
  simp_rw [heq]
  by_cases hT : 0 < T
  · have H := g.source_curve_length_bound haffine hregression independentMarking
      (Paper35.GaussianLayer.gaussianCurveCalculus_of_classical haffine hregression independentMarking hlinear hmax)
      T hT x hx.lipschitzOnWith.absolutelyContinuousOnInterval
    apply H.trans
    calc
      _ ≤ ∫⁻ _t in Icc 0 T, ENNReal.ofReal (g.sourceA : ℝ) := by
        apply lintegral_mono_ae
        filter_upwards [hderiv] with t ht
        rw [ht.deriv]
        apply ENNReal.ofReal_le_ofReal
        exact (Real.sqrt_le_sqrt (g.Q_quadratic_unit_le_sourceA _ (u t) (hu t))).trans_eq
          (Real.sqrt_sq (g.sourceA.property))
      _ = _ := by
        rw [lintegral_const]
        simp only [Measure.restrict_apply_univ,Real.volume_Icc,sub_zero,T,
          ENNReal.ofReal_toReal hfinite,ENNReal.ofReal_coe_nnreal]
  · have hT0 : T=0 := le_antisymm (le_of_not_gt hT) ENNReal.toReal_nonneg
    simp [hT0]

end Paper35.GaussianLayer.Layer

namespace Paper35.DeepModel.Network
lemma measurable_layerCurveLength (m : Paper35.DeepModel.Network) (n : ℕ)
    (η : ℝ → Paper35.DeepModel.Space (m.width n)) (L : ℝ) :
    Measurable (fun θ : m.Parameter n => eVariationOn (fun t => m.layerMap n θ (η t)) (Icc 0 L)) := by
  have hpoint (t : ℝ) : Continuous (fun θ : m.Parameter n => m.layerMap n θ (η t)) := by
    have H := (m.continuous_layerEval n).comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : m.Parameter n => η t)))
    dsimp only [Function.comp_def] at H
    exact H
  apply LowerSemicontinuous.measurable
  unfold eVariationOn
  apply lowerSemicontinuous_iSup
  intro p
  apply Continuous.lowerSemicontinuous
  apply continuous_finset_sum
  intro i hi
  exact (hpoint (p.2.1 (i+1))).edist (hpoint (p.2.1 i))
/-- Deterministic switch-count transport through a monotone arclength
factorization, independent of any weight-law assumptions. -/
lemma layerSwitchCount_reparam_le (m : Paper35.DeepModel.Network) (n : ℕ) (θ : m.Parameter n)
    (η x : ℝ → Paper35.DeepModel.Space (m.width n)) (σ : ℝ → ℝ) (L T : ℝ)
    (hm : MonotoneOn σ (Icc 0 L)) (himage : σ '' Icc 0 L=Icc 0 T)
    (hfactor : EqOn η (x ∘ σ) (Icc 0 L)) :
    m.layerSwitchCount n θ η L ≤ m.layerSwitchCount n θ x T := by
  have heq (r : Fin (m.width (n+1))) :
      Paper35.switchSet (m.layerScores n θ η r) L =
        Paper35.switchSet (fun j => m.layerScores n θ x r j ∘ σ) L := by
    apply Paper35.DeepModel.Network.LayerSource.switchSet_congrOn
    intro j t ht
    dsimp [layerScores,Function.comp_def]
    rw [hfactor ht]
    rfl
  change ((⋃ r, Paper35.switchSet (m.layerScores n θ η r) L).encard : ℝ≥0∞) ≤ _
  simp_rw [heq]
  exact Paper35.ArclengthSwitch.joint_count_comp_le (m.rank n) (m.layerScores n θ x)
    σ L T hm himage

end Paper35.DeepModel.Network

namespace Paper35.GaussianNetwork
open Paper35.DeepModel Paper35.GaussianWinner Paper35.GaussianUnitAdapter
open Paper35.CurveCalculus

structure Model where
  width : ℕ → ℕ
  width_pos : ∀ n, 0 < width n
  layer : (n : ℕ) → Paper35.GaussianLayer.Layer (width n) (width (n+1))
  rank_two : ∀ n r, 1 ≤ (layer n).rankMinusOne r

namespace Model
variable (g : Model)

def parameterToSpace (n : ℕ) (θ : (g.layer n).Parameter) :
    LayerParameter (g.width n) (g.width (n+1)) (fun r => (g.layer n).rankMinusOne r+1) :=
  fun r j => candidateToSpace (θ r j)

lemma measurable_parameterToSpace (n : ℕ) : Measurable (g.parameterToSpace n) := by
  apply measurable_pi_lambda
  intro r
  apply measurable_pi_lambda
  intro j
  exact (measurable_candidateToSpace _).comp ((measurable_pi_apply j).comp (measurable_pi_apply r))

def network : DeepModel.Network where
  width := g.width
  width_pos := g.width_pos
  rank := fun n r => (g.layer n).rankMinusOne r+1
  rank_pos := fun _ _ => Nat.succ_pos _
  layerLaw := fun n => (g.layer n).law.map (g.parameterToSpace n)
  layer_probability := fun n => by
    letI := (g.layer n).probability
    exact Measure.isProbabilityMeasure_map (g.measurable_parameterToSpace n).aemeasurable

lemma layerMap_eq (n : ℕ) (θ : (g.layer n).Parameter) (x : DeepModel.Space (g.width n)) :
    g.network.layerMap n (g.parameterToSpace n θ) x = (g.layer n).layerMap θ x := by
  ext r
  change finiteSup (Nat.succ_pos ((g.layer n).rankMinusOne r))
    (fun j => inner ℝ (WithLp.toLp 2 (θ r j).1) x+(θ r j).2) =
      finiteMax ((g.layer n).rankMinusOne r) ((g.layer n).unit r |>.scores (fun i => x i) (θ r))
  rw [finiteMax_eq_finiteSup]
  congr 1
  funext j
  exact congrArg (fun y => y+(θ r j).2) (Paper35.GaussianLayer.weight_inner_eq (θ r j).1 x)

/-- The actual Euclidean layer law retains exactly the Gaussian marginal of
every unit after the source coordinate transport. -/
lemma marginal (n : ℕ) (r : Fin (g.width (n+1))) :
    (g.network.layerLaw n).map (fun θ => θ r) =
      (independentModel ((g.layer n).unit r)).sampleLaw ((g.layer n).rankMinusOne r+1) := by
  change (((g.layer n).law.map (g.parameterToSpace n)).map (fun θ => θ r)) = _
  rw [Measure.map_map (measurable_pi_apply r) (g.measurable_parameterToSpace n)]
  have H := Measure.map_map (μ := (g.layer n).law) (f := fun θ => θ r)
    (g := sampleToSpace) (measurable_sampleToSpace _) (measurable_pi_apply r)
  rw [(g.layer n).marginal r,sampleLaw_map] at H
  exact H.symm

/-- Gaussian A_G one-layer bound under the actual Network layer law. -/
theorem oneLayer_length_bound (haffine : AffineGaussianLawInput)
    (hregression : GaussianRegressionInput) (harc : ArclengthFactorizationInput)
    (hlinear : LinearACCalculusInput) (hmax : FiniteMaxACCalculusInput)
    (n : ℕ) (η : ℝ → DeepModel.Space (g.width n)) (L : ℝ)
    (hcont : ContinuousOn η (Icc 0 L)) (hfinite : eVariationOn η (Icc 0 L) ≠ ∞) :
    (∫⁻ θ, eVariationOn (fun t => g.network.layerMap n θ (η t)) (Icc 0 L) ∂g.network.layerLaw n) ≤
      ((g.layer n).sourceA : ℝ≥0∞) * eVariationOn η (Icc 0 L) := by
  let f : LayerParameter (g.width n) (g.width (n+1)) (fun r => (g.layer n).rankMinusOne r+1) → ℝ≥0∞ :=
    fun θ => eVariationOn (fun t => g.network.layerMap n θ (η t)) (Icc 0 L)
  have hf : Measurable f := g.network.measurable_layerCurveLength n η L
  have HM := lintegral_map (μ := (g.layer n).law) hf (g.measurable_parameterToSpace n)
  change (∫⁻ θ, f θ ∂(g.layer n).law.map (g.parameterToSpace n)) ≤ _
  rw [HM]
  dsimp only [f]
  simp_rw [g.layerMap_eq]
  exact (g.layer n).rectifiable_length_bound haffine hregression harc hlinear hmax
    (g.width_pos n) η L hcont hfinite

/-- Exact source (8.20) under the actual current Network layer law,
conditional on its deterministic incoming AC curve. -/
theorem curve_length_bound (haffine : AffineGaussianLawInput)
    (hregression : GaussianRegressionInput)
    (hlinear : LinearACCalculusInput) (hmax : FiniteMaxACCalculusInput)
    (n : ℕ) (T : ℝ) (hT : 0 < T) (η : ℝ → DeepModel.Space (g.width n))
    (hη : AbsolutelyContinuousOnInterval η 0 T) :
    (∫⁻ θ, eVariationOn (fun t => g.network.layerMap n θ (η t)) (Icc 0 T) ∂g.network.layerLaw n) ≤
      ∫⁻ s in Icc 0 T, ENNReal.ofReal (Real.sqrt (Paper35.Deep.covarianceForm
        ((g.layer n).totalQ (fun i => η s i))
        (fun i => (deriv η s) i) (fun i => (deriv η s) i))) := by
  let f : LayerParameter (g.width n) (g.width (n+1)) (fun r => (g.layer n).rankMinusOne r+1) → ℝ≥0∞ :=
    fun θ => eVariationOn (fun t => g.network.layerMap n θ (η t)) (Icc 0 T)
  have hf : Measurable f := g.network.measurable_layerCurveLength n η T
  have HM := lintegral_map (μ := (g.layer n).law) hf (g.measurable_parameterToSpace n)
  change (∫⁻ θ, f θ ∂(g.layer n).law.map (g.parameterToSpace n)) ≤ _
  rw [HM]
  dsimp only [f]
  simp_rw [g.layerMap_eq]
  exact (g.layer n).source_curve_length_bound haffine hregression
    Paper35.GaussianWinner.independentMarking
    (Paper35.GaussianLayer.gaussianCurveCalculus_of_classical haffine hregression
      Paper35.GaussianWinner.independentMarking hlinear hmax) T hT η hη

/-- Actual Gaussian expected-length propagation with precisely source A_G. -/
theorem length_propagation (haffine : AffineGaussianLawInput)
    (hregression : GaussianRegressionInput) (harc : ArclengthFactorizationInput)
    (hlinear : LinearACCalculusInput) (hmax : FiniteMaxACCalculusInput)
    (γ : ℝ → DeepModel.Space (g.width 0)) (L : ℝ)
    (hcont : ContinuousOn γ (Icc 0 L)) (hfinite : eVariationOn γ (Icc 0 L) ≠ ∞) :
    ∀ N, g.network.expectedLength N γ L ≤ eVariationOn γ (Icc 0 L) *
      ∏ n ∈ Finset.range N, ((g.layer n).sourceA : ℝ≥0∞) := by
  apply g.network.network_length_propagation (fun n => (g.layer n).sourceA)
  intro n ω
  obtain ⟨C,hC⟩ := g.network.networkMap_lipschitz n ω
  exact g.oneLayer_length_bound haffine hregression harc hlinear hmax n _ L
    (hC.continuous.comp_continuousOn hcont) (hC.comp_boundedVariationOn hfinite)

def switchCost (n : ℕ) (v : DeepModel.Space (g.width n)) : ℝ :=
  ∑ r, Paper35.gaussianRankCoefficient ((g.layer n).rankMinusOne r+1) /
    ((g.layer n).unit r).biasSd * Real.sqrt
      (Paper35.GaussianFactors.quadratic ((g.layer n).unit r).covariance v)

lemma switchCost_nonneg (n : ℕ) (v : DeepModel.Space (g.width n)) : 0 ≤ g.switchCost n v :=
  Finset.sum_nonneg (fun r _ => mul_nonneg
    (div_nonneg (Paper35.gaussianRankCoefficient_nonneg _) ((g.layer n).unit r).biasSd_pos.le)
    (Real.sqrt_nonneg _))

lemma measurable_unitSwitchCost (n : ℕ) (r : Fin (g.width (n+1))) :
    Measurable (fun v : DeepModel.Space (g.width n) =>
      Paper35.gaussianRankCoefficient ((g.layer n).rankMinusOne r+1) /
        ((g.layer n).unit r).biasSd * Real.sqrt
          (Paper35.GaussianFactors.quadratic ((g.layer n).unit r).covariance v)) := by
  unfold Paper35.GaussianFactors.quadratic Paper35.Deep.covarianceForm Matrix.mulVec dotProduct
  fun_prop

lemma switchCost_unit_le (n : ℕ) (v : DeepModel.Space (g.width n)) (hv : ‖v‖=1) :
    g.switchCost n v ≤ ((g.layer n).sourceD : ℝ) :=
  le_csSup (Paper35.GaussianFactors.D_bddAbove _ _ _ (fun r => ((g.layer n).unit r).biasSd_pos)) ⟨v,hv,rfl⟩

/-- The coupled actual layer union-count bound from each original unit's
directional Gaussian theorem. This intermediate assembly permits arbitrary
same-layer dependence. -/
theorem probe_count_from_unit_bounds (hLN : Paper35.ClassicalInputs.LusinNovikovLaw)
    (n : ℕ) (p : Paper35.Source.Probe (g.width n))
    (hunit : ∀ r : Fin (g.width (n+1)),
      (independentModel ((g.layer n).unit r)).expectedCount ((g.layer n).rankMinusOne r+1) p ≤
        ∫⁻ t in Icc 0 p.length, ENNReal.ofReal
          (Paper35.gaussianRankCoefficient ((g.layer n).rankMinusOne r+1) /
            ((g.layer n).unit r).biasSd * Real.sqrt
              (Paper35.GaussianFactors.quadratic ((g.layer n).unit r).covariance (deriv p.curve t)))) :
    (∫⁻ θ, g.network.layerSwitchCount n θ p.curve p.length ∂g.network.layerLaw n) ≤
      ∫⁻ t in Icc 0 p.length, ENNReal.ofReal (g.switchCost n (deriv p.curve t)) := by
  have hc (r : Fin (g.width (n+1))) : Measurable (fun θ : g.network.Parameter n =>
      Paper35.switchCount (g.network.layerScores n θ p.curve r) p.length) :=
    (Paper35.RandomCount.measurable_affineSwitchCount p.curve p.length p.length_pos
      p.lipschitz.continuousOn (hLN _ _)).comp (measurable_pi_apply r)
  calc
    _ ≤ ∑ r, Paper35.expectedSwitchCount (g.network.layerLaw n)
        (fun θ => g.network.layerScores n θ p.curve r) p.length :=
      Paper35.Deep.expected_jointSwitchCount_le (g.network.layerLaw n) (g.network.rank n)
        (fun θ r => g.network.layerScores n θ p.curve r) p.length hc
    _ = ∑ r, (independentModel ((g.layer n).unit r)).expectedCount ((g.layer n).rankMinusOne r+1) p := by
      apply Finset.sum_congr rfl
      intro r hr
      have hm := Paper35.RandomCount.measurable_affineSwitchCount
        (K := (g.layer n).rankMinusOne r+1) p.curve p.length p.length_pos
        p.lipschitz.continuousOn (hLN _ _)
      have H := lintegral_map (μ := g.network.layerLaw n) hm (measurable_pi_apply r)
      rw [g.marginal n r] at H
      exact H.symm
    _ ≤ ∑ r, ∫⁻ t in Icc 0 p.length, ENNReal.ofReal
        (Paper35.gaussianRankCoefficient ((g.layer n).rankMinusOne r+1) /
          ((g.layer n).unit r).biasSd * Real.sqrt
            (Paper35.GaussianFactors.quadratic ((g.layer n).unit r).covariance (deriv p.curve t))) :=
      Finset.sum_le_sum (fun r _ => hunit r)
    _ = _ := by
      simp only [switchCost]
      simp_rw [ENNReal.ofReal_sum_of_nonneg (fun r _ => mul_nonneg
        (div_nonneg (Paper35.gaussianRankCoefficient_nonneg _) ((g.layer n).unit r).biasSd_pos.le)
        (Real.sqrt_nonneg _))]
      exact (lintegral_finset_sum _ (fun r _ =>
        ((g.measurable_unitSwitchCost n r).comp (measurable_deriv p.curve)).ennreal_ofReal)).symm

open Paper35.GaussianLift Paper35.GaussianMarked Paper35.GaussianIndependent
open Paper35.ClassicalInputs

/-- Each actual Gaussian unit's tight directional theorem is combined into
the parallel layer kernel. No per-layer expected-count bound is assumed. -/
theorem probe_count_bound
    (hrep : GaussianRepresentationLaw) (hcrofton : ClassicalCroftonLaw)
    (hregular : ClassicalCroftonRegularityLaw) (hproj : GaussianUnitProjectionLaw)
    (hrot : GaussianPairReconstructionLaw) (hmax : GaussianMaxIntegralLaw)
    (hLN : LusinNovikovLaw) (n : ℕ) (p : Paper35.Source.Probe (g.width n)) :
    (∫⁻ θ, g.network.layerSwitchCount n θ p.curve p.length ∂g.network.layerLaw n) ≤
      ∫⁻ t in Icc 0 p.length, ENNReal.ofReal (g.switchCost n (deriv p.curve t)) := by
  apply g.probe_count_from_unit_bounds hLN n p
  intro r
  have hK : 2 ≤ (g.layer n).rankMinusOne r+1 := by have H := g.rank_two n r; omega
  have H := Paper35.GaussianUnitDirectional.expectedCount_le_directional
    hrep hcrofton hregular hproj hrot hmax ((g.layer n).unit r) (g.width_pos n)
    ((g.layer n).rankMinusOne r+1) hK p (hLN _ _) (fun _ => hLN _ _)
  rw [expectedCount_eq ((g.layer n).unit r) _ p (hLN _ _)] at H
  exact H

/-- The exact source D_G one-layer bound, including arclength compression and
all original-parameter multiplicities of the actual network switch set. -/
theorem oneLayer_count_bound
    (hrep : GaussianRepresentationLaw) (hcrofton : ClassicalCroftonLaw)
    (hregular : ClassicalCroftonRegularityLaw) (hproj : GaussianUnitProjectionLaw)
    (hrot : GaussianPairReconstructionLaw) (hmax : GaussianMaxIntegralLaw)
    (hLN : LusinNovikovLaw) (harc : ArclengthFactorizationInput)
    (n : ℕ) (η : ℝ → DeepModel.Space (g.width n)) (L : ℝ) (hL : 0 ≤ L)
    (hcont : ContinuousOn η (Icc 0 L)) (hfinite : eVariationOn η (Icc 0 L) ≠ ∞) :
    (∫⁻ θ, g.network.layerSwitchCount n θ η L ∂g.network.layerLaw n) ≤
      ((g.layer n).sourceD : ℝ≥0∞) * eVariationOn η (Icc 0 L) := by
  obtain ⟨x,u,σ,hx,hmu,hu,hderiv,hσcont,hσmono,himage,hfactor⟩ :=
    harc _ (g.width_pos n) η L hL hcont hfinite
  let T := (eVariationOn η (Icc 0 L)).toReal
  apply (lintegral_mono (fun θ =>
    g.network.layerSwitchCount_reparam_le n θ η x σ L T hσmono himage hfactor)).trans
  by_cases hT : 0 < T
  · have hvar : eVariationOn x (Icc 0 T)=ENNReal.ofReal T := by
      calc
        _ = eVariationOn (x ∘ σ) (Icc 0 L) := by
          rw [eVariationOn.comp_eq_of_monotoneOn _ _ hσmono,himage]
        _ = eVariationOn η (Icc 0 L) := (eVariationOn.eq_of_eqOn hfactor).symm
        _ = _ := (ENNReal.ofReal_toReal hfinite).symm
    let p : Paper35.Source.Probe (g.width n) := ⟨x,T,hT,hx.lipschitzOnWith,hvar⟩
    calc
      _ ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (g.switchCost n (deriv x t)) :=
        g.probe_count_bound hrep hcrofton hregular hproj hrot hmax hLN n p
      _ = ∫⁻ t in Icc 0 T, ENNReal.ofReal (g.switchCost n (u t)) := by
        apply lintegral_congr_ae
        filter_upwards [hderiv] with t ht
        rw [ht.deriv]
      _ ≤ ∫⁻ _t in Icc 0 T, ENNReal.ofReal ((g.layer n).sourceD : ℝ) :=
        lintegral_mono (fun t => ENNReal.ofReal_le_ofReal (g.switchCost_unit_le n (u t) (hu t)))
      _ = _ := by
        rw [lintegral_const]
        simp only [Measure.restrict_apply_univ,Real.volume_Icc,sub_zero,T,
          ENNReal.ofReal_toReal hfinite,ENNReal.ofReal_coe_nnreal]
  · have hT0 : T=0 := le_antisymm (le_of_not_gt hT) ENNReal.toReal_nonneg
    have heq (θ : g.network.Parameter n) : g.network.layerSwitchCount n θ x T=0 := by
      have hset : g.network.layerSwitchTimes n θ x T=∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro t ht
        rcases mem_iUnion.mp ht with ⟨r,ht0,htT,hrest⟩
        exact (not_lt_of_ge ht0.le) (hT0 ▸ htT)
      simp [DeepModel.Network.layerSwitchCount,hset]
    simp_rw [heq]
    simp

/-- Corollary 8.3, source (8.19), for the actual independently sampled deep
Gaussian Maxout network, with the exact factors (8.17) and (8.18). -/
theorem switch_propagation
    (haffine : AffineGaussianLawInput) (hregression : GaussianRegressionInput)
    (hrep : GaussianRepresentationLaw) (hcrofton : ClassicalCroftonLaw)
    (hregular : ClassicalCroftonRegularityLaw) (hproj : GaussianUnitProjectionLaw)
    (hrot : GaussianPairReconstructionLaw) (hmaxG : GaussianMaxIntegralLaw)
    (hLN : LusinNovikovLaw) (harc : ArclengthFactorizationInput)
    (hlinear : LinearACCalculusInput) (hmaxAC : FiniteMaxACCalculusInput)
    (γ : ℝ → DeepModel.Space (g.width 0)) (L : ℝ) (hL : 0 ≤ L)
    (hcont : ContinuousOn γ (Icc 0 L)) (hfinite : eVariationOn γ (Icc 0 L) ≠ ∞) :
    ∀ N, g.network.expectedCount N γ L ≤ eVariationOn γ (Icc 0 L) *
      ∑ n ∈ Finset.range N, ((g.layer n).sourceD : ℝ≥0∞) *
        ∏ k ∈ Finset.range n, ((g.layer k).sourceA : ℝ≥0∞) := by
  apply g.network.network_switch_propagation (fun n => (g.layer n).sourceA) (fun n => (g.layer n).sourceD)
  · intro n ω
    obtain ⟨C,hC⟩ := g.network.networkMap_lipschitz n ω
    exact g.oneLayer_length_bound haffine hregression harc hlinear hmaxAC n _ L
      (hC.continuous.comp_continuousOn hcont) (hC.comp_boundedVariationOn hfinite)
  · intro n ω
    obtain ⟨C,hC⟩ := g.network.networkMap_lipschitz n ω
    exact g.oneLayer_count_bound hrep hcrofton hregular hproj hrot hmaxG hLN harc n _ L hL
      (hC.continuous.comp_continuousOn hcont) (hC.comp_boundedVariationOn hfinite)

/-- The actual Gaussian network length expectation is finite; this follows
from the proved source A_G product bound and introduces no moment premise. -/
theorem expectedLength_lt_top
    (haffine : AffineGaussianLawInput) (hregression : GaussianRegressionInput)
    (harc : ArclengthFactorizationInput) (hlinear : LinearACCalculusInput)
    (hmaxAC : FiniteMaxACCalculusInput)
    (γ : ℝ → DeepModel.Space (g.width 0)) (L : ℝ)
    (hcont : ContinuousOn γ (Icc 0 L)) (hfinite : eVariationOn γ (Icc 0 L) ≠ ∞) (N : ℕ) :
    g.network.expectedLength N γ L < ∞ :=
  (g.length_propagation haffine hregression harc hlinear hmaxAC γ L hcont hfinite N).trans_lt
    (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hfinite)
      (ENNReal.prod_lt_top (fun _ _ => ENNReal.coe_lt_top)))

/-- The actual Gaussian union-count expectation is finite, including singular
weight covariances and arbitrary same-layer dependence. -/
theorem expectedCount_lt_top
    (haffine : AffineGaussianLawInput) (hregression : GaussianRegressionInput)
    (hrep : GaussianRepresentationLaw) (hcrofton : ClassicalCroftonLaw)
    (hregular : ClassicalCroftonRegularityLaw) (hproj : GaussianUnitProjectionLaw)
    (hrot : GaussianPairReconstructionLaw) (hmaxG : GaussianMaxIntegralLaw)
    (hLN : LusinNovikovLaw) (harc : ArclengthFactorizationInput)
    (hlinear : LinearACCalculusInput) (hmaxAC : FiniteMaxACCalculusInput)
    (γ : ℝ → DeepModel.Space (g.width 0)) (L : ℝ) (hL : 0 ≤ L)
    (hcont : ContinuousOn γ (Icc 0 L)) (hfinite : eVariationOn γ (Icc 0 L) ≠ ∞) (N : ℕ) :
    g.network.expectedCount N γ L < ∞ := by
  apply (g.switch_propagation haffine hregression hrep hcrofton hregular hproj hrot hmaxG
    hLN harc hlinear hmaxAC γ L hL hcont hfinite N).trans_lt
  apply ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hfinite)
  apply ENNReal.sum_lt_top.mpr
  intro n hn
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top
    (ENNReal.prod_lt_top (fun _ _ => ENNReal.coe_lt_top))

/-- Both extended source bounds are exactly ordinary, integrable real
expectations of the actual Gaussian network count and curve length. This
eliminates any finite-expectation or measurability premise from the source
reading of (8.19), (8.20), and the A_G length propagation. -/
theorem ordinary_expectations
    (haffine : AffineGaussianLawInput) (hregression : GaussianRegressionInput)
    (hrep : GaussianRepresentationLaw) (hcrofton : ClassicalCroftonLaw)
    (hregular : ClassicalCroftonRegularityLaw) (hproj : GaussianUnitProjectionLaw)
    (hrot : GaussianPairReconstructionLaw) (hmaxG : GaussianMaxIntegralLaw)
    (hLN : LusinNovikovLaw) (harc : ArclengthFactorizationInput)
    (hlinear : LinearACCalculusInput) (hmaxAC : FiniteMaxACCalculusInput)
    (γ : ℝ → DeepModel.Space (g.width 0)) (L : ℝ) (hL : 0 < L)
    (hcont : ContinuousOn γ (Icc 0 L)) (hfinite : eVariationOn γ (Icc 0 L) ≠ ∞) (N : ℕ) :
    Integrable (fun ω => (g.network.switchCount N ω γ L).toReal) (g.network.law N) ∧
    Integrable (fun ω => (g.network.curveLength N ω γ L).toReal) (g.network.law N) ∧
    g.network.expectedCount N γ L = ENNReal.ofReal
      (∫ ω, (g.network.switchCount N ω γ L).toReal ∂g.network.law N) ∧
    g.network.expectedLength N γ L = ENNReal.ofReal
      (∫ ω, (g.network.curveLength N ω γ L).toReal ∂g.network.law N) := by
  have hC := g.expectedCount_lt_top haffine hregression hrep hcrofton hregular hproj hrot hmaxG
    hLN harc hlinear hmaxAC γ L hL.le hcont hfinite N
  have hA := g.expectedLength_lt_top haffine hregression harc hlinear hmaxAC γ L hcont hfinite N
  exact ⟨integrable_toReal_of_lintegral_ne_top
      (g.network.measurable_switchCount hLN N γ L hL hcont).aemeasurable hC.ne,
    integrable_toReal_of_lintegral_ne_top (g.network.measurable_curveLength N γ L).aemeasurable hA.ne,
    g.network.expectedCount_eq_integral hLN N γ L hL hcont hC,
    g.network.expectedLength_eq_integral N γ L hA⟩

end Model
end Paper35.GaussianNetwork
