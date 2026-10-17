import Paper35.DeepSwitch
import Paper35.CovarianceSpectral
import Paper35.GaussianSpectrum

/-! The actual uncentered weight second-moment matrix controls the source A
factor. The maximum-to-sum and moment/matrix identification are proved here. -/
noncomputable section
open MeasureTheory Matrix Set
open scoped BigOperators ENNReal NNReal
namespace Paper35.DeepModel.Network
open Paper35.Deep
variable (m : DeepModel.Network)

def candidateSecondMoment (n : ℕ) (r : Fin (m.width (n+1))) (j : Fin (m.rank n r)) :
    Matrix (Fin (m.width n)) (Fin (m.width n)) ℝ :=
  fun i k => ∫ θ : m.Parameter n, (θ r j).1 i*(θ r j).1 k ∂m.layerLaw n

def totalSecondMoment (n : ℕ) : Matrix (Fin (m.width n)) (Fin (m.width n)) ℝ :=
  ∑ r, ∑ j, m.candidateSecondMoment n r j

lemma inner_square_moment (n : ℕ) (r : Fin (m.width (n+1))) (j : Fin (m.rank n r))
    (hW : MemLp (fun θ : m.Parameter n => (θ r j).1) 2 (m.layerLaw n))
    (v : Space (m.width n)) :
    (∫ θ : m.Parameter n, |inner ℝ v (θ r j).1|^2 ∂m.layerLaw n) =
      covarianceForm (m.candidateSecondMoment n r j) (fun i => v i) (fun i => v i) := by
  have hcoord (i : Fin (m.width n)) :
      MemLp (fun θ : m.Parameter n => (θ r j).1 i) 2 (m.layerLaw n) :=
    (memLp_piLp_iff.mp hW) i
  have H := Paper35.GaussianWinner.integral_dotProduct_square (m.layerLaw n)
    (fun θ i => (θ r j).1 i) hcoord (fun i => v i)
  convert H using 1
  congr 1
  funext θ
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial,sq_abs]
  rw [dotProduct_comm]
  rfl

lemma candidateSecondMoment_posSemidef (n : ℕ) (r : Fin (m.width (n+1))) (j : Fin (m.rank n r))
    (hW : MemLp (fun θ : m.Parameter n => (θ r j).1) 2 (m.layerLaw n)) :
    (m.candidateSecondMoment n r j).PosSemidef := by
  constructor
  · ext i k
    change (∫ θ : m.Parameter n, (θ r j).1 k*(θ r j).1 i ∂m.layerLaw n) =
      ∫ θ : m.Parameter n, (θ r j).1 i*(θ r j).1 k ∂m.layerLaw n
    simp only [mul_comm]
  · intro v
    have H := m.inner_square_moment n r j hW (WithLp.toLp 2 v)
    simp only [PiLp.toLp_apply] at H
    change 0 ≤ covarianceForm (m.candidateSecondMoment n r j) v v
    rw [← H]
    exact integral_nonneg (fun θ => sq_nonneg _)

lemma totalSecondMoment_posSemidef (n : ℕ)
    (hW : ∀ r j, MemLp (fun θ : m.Parameter n => (θ r j).1) 2 (m.layerLaw n)) :
    (m.totalSecondMoment n).PosSemidef := by
  constructor
  · ext i k
    simp only [totalSecondMoment,Matrix.conjTranspose_apply,star_trivial,Matrix.sum_apply,
      candidateSecondMoment,mul_comm]
  · intro v
    change 0 ≤ covarianceForm (m.totalSecondMoment n) v v
    simp only [totalSecondMoment,covarianceForm,Matrix.sum_mulVec,dotProduct_sum]
    exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun j _ =>
      (m.candidateSecondMoment_posSemidef n r j (hW r j)).2 v))

/-- The own maximum-to-sum estimate with the actual source moment matrix. -/
theorem directionalEnergy_le_secondMoment (n : ℕ)
    (hW : ∀ r j, MemLp (fun θ : m.Parameter n => (θ r j).1) 2 (m.layerLaw n))
    (v : Space (m.width n)) :
    m.directionalEnergy n v ≤
      covarianceForm (m.totalSecondMoment n) (fun i => v i) (fun i => v i) := by
  calc
    _ ≤ ∑ r, ∑ j, ∫ θ : m.Parameter n, |inner ℝ v (θ r j).1|^2 ∂m.layerLaw n := by
      apply Finset.sum_le_sum
      intro r hr
      calc
        _ ≤ ∫ θ : m.Parameter n, ∑ j, |inner ℝ v (θ r j).1|^2 ∂m.layerLaw n := by
          apply integral_mono (m.maxProjectedSquare_integrable n v hW r)
            (integrable_finset_sum _ (fun j _ => by
              simpa only [sq_abs] using ((hW r j).const_inner v).integrable_sq))
          intro θ
          exact Finset.sup'_le _ _ (fun j hj =>
            Finset.single_le_sum (fun k _ => sq_nonneg |inner ℝ v (θ r k).1|) hj)
        _ = _ := integral_finset_sum _ (fun j _ => by
          simpa only [sq_abs] using ((hW r j).const_inner v).integrable_sq)
    _ = _ := by
      simp_rw [m.inner_square_moment n _ _ (hW _ _) v]
      simp only [totalSecondMoment,covarianceForm,Matrix.sum_mulVec,dotProduct_sum]

/-- The invariant operator norm of the actual PSD uncentered moment matrix.
For a PSD matrix this is its ordinary largest eigenvalue. -/
def secondMomentSpectralNorm (n : ℕ) : ℝ :=
  ‖(Matrix.toEuclideanLin (m.totalSecondMoment n)).toContinuousLinearMap‖

lemma moment_quadratic_unit_le_spectral (n : ℕ) (v : Space (m.width n)) (hv : ‖v‖=1) :
    covarianceForm (m.totalSecondMoment n) (fun i => v i) (fun i => v i) ≤
      m.secondMomentSpectralNorm n := by
  let T := (Matrix.toEuclideanLin (m.totalSecondMoment n)).toContinuousLinearMap
  have heq : covarianceForm (m.totalSecondMoment n) (fun i => v i) (fun i => v i) =
      inner ℝ v (T v) := by
    simp only [covarianceForm,EuclideanSpace.inner_eq_star_dotProduct,star_trivial,
      T,LinearMap.coe_toContinuousLinearMap,Matrix.toEuclideanLin_apply]
    exact dotProduct_comm _ _
  rw [heq]
  calc
    _ ≤ |inner ℝ v (T v)| := le_abs_self _
    _ ≤ ‖v‖*‖T v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v‖*(‖T‖*‖v‖) := mul_le_mul_of_nonneg_left (T.le_opNorm v) (norm_nonneg _)
    _ = _ := by simp only [hv,one_mul,mul_one]; rfl

/-- Source rough length-factor estimate (8.9), in invariant PSD spectral norm
form. All maximum/expectation/matrix steps are proved. -/
theorem lengthFactor_le_spectral (n : ℕ)
    (hW : ∀ r j, MemLp (fun θ : m.Parameter n => (θ r j).1) 2 (m.layerLaw n)) :
    m.lengthFactor n ≤ Real.sqrt (m.secondMomentSpectralNorm n) := by
  apply csSup_le
  · let v : Space (m.width n) := EuclideanSpace.single ⟨0,m.width_pos n⟩ 1
    exact ⟨_,v,by simp [v,EuclideanSpace.norm_single],rfl⟩
  · rintro a ⟨v,hv,rfl⟩
    exact Real.sqrt_le_sqrt ((m.directionalEnergy_le_secondMoment n hW v).trans
      (m.moment_quadratic_unit_le_spectral n v hv))

/-- The spectral bound is exactly the largest PSD eigenvalue: an actual unit
eigenvector exists, and every eigenvalue is at most it. -/
theorem secondMomentSpectralNorm_maxEigenvalue (n : ℕ)
    (hW : ∀ r j, MemLp (fun θ : m.Parameter n => (θ r j).1) 2 (m.layerLaw n)) :
    (∃ v : Space (m.width n), ‖v‖=1 ∧
      Paper35.GaussianIndependent.covarianceOperator (m.totalSecondMoment n) v =
        m.secondMomentSpectralNorm n • v) ∧
    (∀ (a : ℝ) (v : Space (m.width n)), v ≠ 0 →
      Paper35.GaussianIndependent.covarianceOperator (m.totalSecondMoment n) v = a • v →
        a ≤ m.secondMomentSpectralNorm n) := by
  exact ⟨Paper35.GaussianIndependent.covarianceMax_eigenvector_of_dimension _
      (m.totalSecondMoment_posSemidef n hW) (m.width_pos n),
    fun a v hv he => Paper35.GaussianIndependent.eigenvalue_le_covarianceMax _
      (m.totalSecondMoment_posSemidef n hW) hv he⟩

namespace LayerSource
open Paper35.Source Paper35.Source.WeightedModel
variable {m : DeepModel.Network} {n : ℕ} (a : m.LayerSource n)

/-- Conditional density normalization gives the exact original weight marginal. -/
lemma joint_map_weight {d : ℕ} (b : WeightedModel d) :
    b.joint.map Prod.fst = b.weights := by
  letI := b.probability
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf measurable_fst]
  have H := Paper35.VisibleCrossing.lintegral_joint b (hf.comp measurable_fst)
  dsimp only [Function.comp_def] at H
  rw [H]
  calc
    _ = ∫⁻ w, (∫⁻ t, b.g w t)*f w ∂b.weights := by
      apply lintegral_congr
      intro w
      exact lintegral_mul_const (f w) (b.measurable_g.comp (measurable_const.prodMk measurable_id))
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [b.normalized_g] with w hw
      rw [hw,one_mul]

/-- The uncentered second moment of one actual original weight. -/
def unitSecondMoment (r : Fin (m.width (n+1))) : Matrix (Fin (m.width n)) (Fin (m.width n)) ℝ :=
  fun i k => ∫ w, w i*w k ∂(a.unit r).weights

/-- Every iid candidate has exactly the same actual weight second moment;
the joint law of different units remains arbitrary. -/
lemma candidateSecondMoment_eq_unit (r : Fin (m.width (n+1))) (j : Fin (m.rank n r)) :
    m.candidateSecondMoment n r j = a.unitSecondMoment r := by
  ext i k
  have hm1 : AEStronglyMeasurable (fun ξ : Fin (m.rank n r) → Candidate (m.width n) =>
      (ξ j).1 i*(ξ j).1 k) ((m.layerLaw n).map (fun θ => θ r)) := by fun_prop
  have H1 := integral_map (μ := m.layerLaw n) (measurable_pi_apply r).aemeasurable hm1
  rw [a.marginal r] at H1
  have H2 := integral_map (μ := (a.unit r).iid (m.rank n r))
    (measurable_pi_apply j).aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun ξ : Candidate (m.width n) => ξ.1 i*ξ.1 k)
      (((a.unit r).iid (m.rank n r)).map (fun ξ => ξ j)))
  rw [Paper35.Source.WeightedModel.iid] at H2
  rw [(measurePreserving_eval (fun _ : Fin (m.rank n r) => (a.unit r).joint) j).map_eq] at H2
  have H3 := integral_map (μ := (a.unit r).joint) measurable_fst.aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun w : Space (m.width n) => w i*w k)
      ((a.unit r).joint.map Prod.fst))
  rw [joint_map_weight] at H3
  exact H1.symm.trans (H2.symm.trans H3.symm)

lemma totalSecondMoment_eq_rank_sum :
    m.totalSecondMoment n = ∑ r, (m.rank n r : ℝ) • a.unitSecondMoment r := by
  simp only [totalSecondMoment,a.candidateSecondMoment_eq_unit,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,Nat.cast_smul_eq_nsmul]

/-- Original-weight L² hypotheses imply the actual coupled candidate L²
hypotheses; arbitrary dependence between units has no effect. -/
lemma candidateWeight_map (r : Fin (m.width (n+1))) (j : Fin (m.rank n r)) :
    (m.layerLaw n).map (fun θ => (θ r j).1) = (a.unit r).weights := by
  calc
    _ = (((m.layerLaw n).map (fun θ => θ r)).map (fun ξ => ξ j)).map Prod.fst := by
      rw [Measure.map_map measurable_fst (measurable_pi_apply j)]
      have H := Measure.map_map (μ := m.layerLaw n) (f := fun θ => θ r)
        (g := fun ξ : Fin (m.rank n r) → Candidate (m.width n) => (ξ j).1)
        (by fun_prop) (measurable_pi_apply r)
      simpa only [Function.comp_def] using H.symm
    _ = _ := by
      rw [a.marginal r,Paper35.Source.WeightedModel.iid,
        (measurePreserving_eval (fun _ : Fin (m.rank n r) => (a.unit r).joint) j).map_eq,
        joint_map_weight]

lemma candidateWeight_memLp
    (hW : ∀ r, MemLp (fun w => w) 2 (a.unit r).weights)
    (r : Fin (m.width (n+1))) (j : Fin (m.rank n r)) :
    MemLp (fun θ : m.Parameter n => (θ r j).1) 2 (m.layerLaw n) := by
  have H : MemLp (fun w => w) 2 ((m.layerLaw n).map (fun θ => (θ r j).1)) := by
    rw [a.candidateWeight_map r j]
    exact hW r
  exact H.comp_of_map (by fun_prop : Measurable (fun θ : m.Parameter n => (θ r j).1)).aemeasurable

/-- Exact identification with the outside-half source definition (8.3). -/
lemma sourceD_eq_paper : a.sourceD = (1/2 : ℝ≥0∞) *
    sSup ((fun u : Space (m.width n) => ∑ r,
      (m.rank n r : ℝ≥0∞)*a.B r*(a.unit r).directionalGini u) '' {u | ‖u‖=1}) := by
  have heq (u : Space (m.width n)) : a.directionalCost u = (1/2 : ℝ≥0∞) *
      ∑ r, (m.rank n r : ℝ≥0∞)*a.B r*(a.unit r).directionalGini u := by
    rw [directionalCost,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [div_eq_mul_inv,one_mul]
    ac_rfl
  simp only [sourceD,sSup_image,heq,ENNReal.mul_iSup]

lemma directionalGini_eq_original (r : Fin (m.width (n+1))) (u : Space (m.width n)) :
    (a.unit r).directionalGini u =
      ∫⁻ w, ∫⁻ w', ENNReal.ofReal |inner ℝ u (w-w')| ∂(a.unit r).weights ∂(a.unit r).weights := by
  unfold Paper35.Source.WeightedModel.directionalGini
  rw [tilted_eq_weights_of_constant (a.unit r) (a.B r) (a.envelope r)]

/-- Exact original-law reading of source (8.3), with the independent-copy
product represented by its two original weight-law integrals. -/
lemma sourceD_eq_original : a.sourceD = (1/2 : ℝ≥0∞) *
    sSup ((fun u : Space (m.width n) => ∑ r,
      (m.rank n r : ℝ≥0∞)*a.B r *
        ∫⁻ w, ∫⁻ w', ENNReal.ofReal |inner ℝ u (w-w')| ∂(a.unit r).weights ∂(a.unit r).weights) ''
          {u | ‖u‖=1}) := by
  simpa only [a.directionalGini_eq_original] using a.sourceD_eq_paper

lemma sourceA_coe_original
    (hW : ∀ r, MemLp (fun w => w) 2 (a.unit r).weights) :
    (m.sourceA n : ℝ) = m.lengthFactor n :=
  Real.coe_toNNReal _ (m.lengthFactor_nonneg n (fun r j => a.candidateWeight_memLp hW r j))

/-- The true source D is finite under the original weight L² hypotheses. -/
theorem sourceD_lt_top (hW : ∀ r, MemLp (fun w => w) 2 (a.unit r).weights) :
    a.sourceD < ∞ := by
  let B : ℝ≥0∞ := ∑ r, (m.rank n r : ℝ≥0∞)*a.B r *
    ENNReal.ofReal (Real.sqrt (a.unit r).covarianceSpectralNorm)
  have hsup : sSup (a.covarianceSum '' {u | ‖u‖=1}) ≤ B := by
    apply sSup_le
    rintro b ⟨u,hu,rfl⟩
    apply Finset.sum_le_sum
    intro r hr
    have ht : MemLp (fun w => w) 2 (a.unit r).tilted := by
      rw [tilted_eq_weights_of_constant (a.unit r) (a.B r) (a.envelope r)]
      exact hW r
    apply mul_le_mul_left'
    apply ENNReal.ofReal_le_ofReal
    apply Real.sqrt_le_sqrt
    rw [← Paper35.RandomProbes.projectedVariance_eq_original_of_constant (a.unit r) (a.B r) (a.envelope r)]
    exact (a.unit r).projectedVariance_le_spectral_of_norm_le_one ht u hu.le
  have hbound := (a.sourceD_le_covariance_sup hW).trans (mul_le_mul_left' hsup (1/ENNReal.ofReal (Real.sqrt 3)))
  have hB : B < ∞ := by
    apply ENNReal.sum_lt_top.mpr
    intro r hr
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) ENNReal.coe_lt_top) ENNReal.ofReal_lt_top
  have hc : (1/ENNReal.ofReal (Real.sqrt 3) : ℝ≥0∞) < ∞ := by
    apply ENNReal.div_lt_top
    · simp
    · exact (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<3))).ne'
  exact hbound.trans_lt (ENNReal.mul_lt_top hc hB)

/-- Equation (8.9) with the exact source matrix Σ_r K_r E[W_r W_rᵀ]. -/
theorem lengthFactor_le_rank_secondMoment
    (hW : ∀ r j, MemLp (fun θ : m.Parameter n => (θ r j).1) 2 (m.layerLaw n)) :
    m.lengthFactor n ≤ Real.sqrt (Paper35.GaussianIndependent.covarianceMax
      (∑ r, (m.rank n r : ℝ) • a.unitSecondMoment r)) := by
  have H := m.lengthFactor_le_spectral n hW
  rw [secondMomentSpectralNorm,a.totalSecondMoment_eq_rank_sum] at H
  exact H

end LayerSource
/-- Source (8.6) under exactly the original per-unit weight L² assumptions. -/
theorem source_network_length_bound_original
    (harc : Paper35.CurveCalculus.ArclengthFactorizationInput)
    (hlinear : Paper35.CurveCalculus.LinearACCalculusInput)
    (hmax : Paper35.CurveCalculus.FiniteMaxACCalculusInput)
    (models : ∀ n, m.LayerSource n)
    (hW : ∀ n r, MemLp (fun w => w) 2 ((models n).unit r).weights)
    (γ : ℝ → Space (m.width 0)) (L : ℝ)
    (hcont : ContinuousOn γ (Icc 0 L)) (hfinite : eVariationOn γ (Icc 0 L) ≠ ∞) :
    ∀ N, m.expectedLength N γ L ≤ eVariationOn γ (Icc 0 L) *
      ∏ n ∈ Finset.range N, (m.sourceA n : ℝ≥0∞) :=
  m.source_network_length_bound_classical harc hlinear hmax
    (fun n r j => (models n).candidateWeight_memLp (hW n) r j) γ L hcont hfinite

/-- Source (8.7) under exactly the original per-unit weight L² assumptions. -/
theorem source_network_switch_bound_original
    (hLN : Paper35.ClassicalInputs.LusinNovikovLaw) (hUP : Paper35.ClassicalInputs.BorelProjectionLaw)
    (harc : Paper35.CurveCalculus.ArclengthFactorizationInput)
    (hlinear : Paper35.CurveCalculus.LinearACCalculusInput)
    (hmax : Paper35.CurveCalculus.FiniteMaxACCalculusInput)
    (models : ∀ n, m.LayerSource n)
    (hW : ∀ n r, MemLp (fun w => w) 2 ((models n).unit r).weights)
    (γ : ℝ → Space (m.width 0)) (L : ℝ) (hL : 0 ≤ L)
    (hcont : ContinuousOn γ (Icc 0 L)) (hfinite : eVariationOn γ (Icc 0 L) ≠ ∞) :
    ∀ N, m.expectedCount N γ L ≤ eVariationOn γ (Icc 0 L) *
      ∑ n ∈ Finset.range N, (models n).sourceD *
        ∏ k ∈ Finset.range n, (m.sourceA k : ℝ≥0∞) :=
  m.source_network_switch_bound hLN hUP harc hlinear hmax models
    (fun n r j => (models n).candidateWeight_memLp (hW n) r j) γ L hL hcont hfinite

/-- Finiteness of the actual length expectation, not an additional assumption. -/
theorem expectedLength_lt_top_of_source
    (harc : Paper35.CurveCalculus.ArclengthFactorizationInput)
    (hlinear : Paper35.CurveCalculus.LinearACCalculusInput)
    (hmax : Paper35.CurveCalculus.FiniteMaxACCalculusInput)
    (models : ∀ n, m.LayerSource n)
    (hW : ∀ n r, MemLp (fun w => w) 2 ((models n).unit r).weights)
    (γ : ℝ → Space (m.width 0)) (L : ℝ)
    (hcont : ContinuousOn γ (Icc 0 L)) (hfinite : eVariationOn γ (Icc 0 L) ≠ ∞) (N : ℕ) :
    m.expectedLength N γ L < ∞ :=
  (m.source_network_length_bound_original harc hlinear hmax models hW γ L hcont hfinite N).trans_lt
    (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hfinite) (ENNReal.prod_lt_top (fun _ _ => ENNReal.coe_lt_top)))

/-- Finiteness of the actual original union-count expectation follows from
the proved source factor bounds and original weight moments. -/
theorem expectedCount_lt_top_of_source
    (hLN : Paper35.ClassicalInputs.LusinNovikovLaw) (hUP : Paper35.ClassicalInputs.BorelProjectionLaw)
    (harc : Paper35.CurveCalculus.ArclengthFactorizationInput)
    (hlinear : Paper35.CurveCalculus.LinearACCalculusInput)
    (hmax : Paper35.CurveCalculus.FiniteMaxACCalculusInput)
    (models : ∀ n, m.LayerSource n)
    (hW : ∀ n r, MemLp (fun w => w) 2 ((models n).unit r).weights)
    (γ : ℝ → Space (m.width 0)) (L : ℝ) (hL : 0 ≤ L)
    (hcont : ContinuousOn γ (Icc 0 L)) (hfinite : eVariationOn γ (Icc 0 L) ≠ ∞) (N : ℕ) :
    m.expectedCount N γ L < ∞ := by
  apply (m.source_network_switch_bound_original hLN hUP harc hlinear hmax models hW γ L hL hcont hfinite N).trans_lt
  apply ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hfinite)
  apply ENNReal.sum_lt_top.mpr
  intro n hn
  exact ENNReal.mul_lt_top ((models n).sourceD_lt_top (hW n))
    (ENNReal.prod_lt_top (fun _ _ => ENNReal.coe_lt_top))

end Paper35.DeepModel.Network
